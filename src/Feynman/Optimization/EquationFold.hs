module Feynman.Optimization.EquationFold where

import Data.List hiding (transpose)
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Control.Monad.Writer
import Data.Bits
import Data.Function (fix)
import System.IO.Unsafe
import System.Random

import Debug.Trace

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial.Multilinear as P
import Feynman.Synthesis.Phase

{-- Equation folding optimization -}
{- The State folding optimization is not confluent w.r.t. the choice
   of which variables to contract in which order. This is because
   contracting a particular path with [HH] makes certain phases
   no longer have a representative, when in reality if a different
   variable had been contracted it's possible they can merge.
   The idea here is to find *all* equations which hold between variables
   and canonicalize the term expressions over these.

   Note that since we only apply reductions once now, we're going
   back to the old style of computing a phase polynomial only once -}

data Ctx = Ctx {
  dim   :: Int,
  ket   :: Map ID (F2Vec, Bool),
  terms :: Map F2Vec (Set (Loc, Bool), Angle),
  quad  :: Map Int (F2Vec, Bool),
  phase :: Angle
} deriving Show

data PathState = PathState {
  pvars :: [Int],
  pp    :: PseudoBoolean String Angle,
  st    :: [SBool String]
} deriving (Eq, Ord, Show)

----------------------------------------------------------------------
{- The initial phase analysis -}

-- Allocate a new variable
alloc :: State Ctx Int
alloc = do
  n <- gets dim
  modify $ \st -> st { dim = n + 1 }
  return n

-- Get the state of variable v
getSt :: ID -> State Ctx (F2Vec, Bool)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do
      n <- alloc
      modify $ \st -> st { ket = Map.insert v (bit n, False) (ket st) }
      return (bit n, False)


  -- Set the state of a variable
setSt :: ID -> (F2Vec, Bool) -> State Ctx ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv (ket st) }

-- Adds a mergeable phase term
addTerm :: Angle -> Loc -> (F2Vec, Bool) -> State Ctx ()
addTerm theta loc (bv, parity) = modify go where
  go st = case parity of
    False -> st { terms = Map.alter (add theta) bv (terms st) }
    True  -> st { terms = Map.alter (add (-theta)) bv (terms st),
                  phase = (phase st) + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, parity), theta)

-- Adds a quadratic phase term
addQuadTerm :: Int -> (F2Vec, Bool) -> State Ctx ()
addQuadTerm n bv = modify $ \st -> st { quad = Map.insert n bv $ quad st }

-- Applies a gate to a context
applyGate :: (Primitive, Loc) -> State Ctx ()
applyGate (gate, l) = case gate of
  T v    -> getSt v >>= addTerm (Discrete $ dMod2 1 2) l
  Tinv v -> getSt v >>= addTerm (Discrete $ dMod2 7 2) l
  S v    -> getSt v >>= addTerm (Discrete $ dMod2 1 1) l
  Sinv v -> getSt v >>= addTerm (Discrete $ dMod2 3 1) l
  Z v    -> getSt v >>= addTerm (Discrete $ dMod2 1 0) l
  Rz p v -> getSt v >>= addTerm p l
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (fst bv + fst bv', snd bv `xor` snd bv')
  X v      -> do
    bv <- getSt v
    setSt v (fst bv, Prelude.not $ snd bv)
  H v      -> do
    bv <- getSt v
    n <- alloc
    setSt v (bit n, False)
    addQuadTerm n bv
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _      -> error "Unsupported gate"

-- Run the analysis on a circuit and state
applyCircuit :: [Primitive] -> State Ctx ()
applyCircuit circ = mapM_ applyGate (zip circ [2..])

----------------------------------------------------------------------
{- Equational reduction phase -}

-- The /i/th variable
var :: Int -> String
var i = "v" ++ show i

-- The number of a variable
unvar :: String -> Int
unvar = read . tail

-- Compute a phase polynomial from the state
computePP :: Ctx -> PseudoBoolean String Angle
computePP st = foldl' (+) (constant $ phase st) $ l ++ q where
  l = map go . Map.toList $ terms st where
    go (bv, (_,theta)) = distribute theta (toPolynomial (bv, False))
  q = map go . Map.toList $ quad st where
    go (n, v) = distribute (Discrete $ dMod2 1 0) poly where
      poly = ofVar (var n) * toPolynomial v

-- Converts a bitvector into a polynomial
toPolynomial :: (F2Vec, Bool) -> SBool String
toPolynomial bv = foldr (+) const . map (ofVar . var) . varsOfBV $ fst bv
  where const = if snd bv then 1 else 0

-- Substitute a variable
substVar :: Int -> (F2Vec, Bool) -> State Ctx ()
substVar x bv = modify go where
  go st = st { terms = Map.mapKeysWith add substKey $ terms st,
               ket   = Map.map substState $ ket st }
  add (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)
  substKey bv' = case testBit bv' x of
    False -> bv'
    True  -> (complementBit bv' x) + (fst bv)
  substState bv = (substKey $ fst bv, snd bv)

-- Converts a Boolean polynomial into a (symbolic) bitvector
-- The idea is to package high degree terms into unique variables
-- so that we maintain a linear presentation, later possibly
-- subject to equalities
linearize :: SBool String -> State Ctx (F2Vec, Bool)
linearize = foldM go (bitI 0 0, False) . P.support where
  go (bv, parity) mono
    | degree mono == 0 = return (bv, parity `xor` True)
    | degree mono == 1 = do
        let v = unvar . head . Set.toList . vars $ mono
        return (bv `xor` (bit v), parity)
    | otherwise = do
        n <- alloc
        return (bv `xor` (bit n), parity)

injectZ2 :: Periodic a => a -> Maybe FF2
injectZ2 a = case order a of
  0 -> Just 0
  2 -> Just 1
  _ -> Nothing

--toBooleanPoly :: (Eq a, Periodic a) => PseudoBoolean String a -> Maybe (SBool v)
toBooleanPoly = castMaybe injectZ2

-- Gets the variables in a bitvector
varsOfBV :: F2Vec -> [Int]
varsOfBV bv = Set.toList . Set.fromList $ filter (testBit bv) [0..(width bv) - 1]

-- Converts a linear Boolean polynomial into a bitvector
fromPolynomial :: SBool String -> Maybe (F2Vec, Bool)
fromPolynomial p
  | degree p > 1 = Nothing
  | otherwise    = Just $ unsafeConvert p
    where unsafeConvert = (foldl' f (bitI 0 0, False)). P.toTermList
          f (bv, const) (b, m)
            | b == 0      = (bv, const)
            | m == mempty = (bv, const `xor` True)
            | otherwise   =
              let v = unvar . head . Set.toList . vars $ m in
                (bv `xor` (bitI (v+1) v), const)

---------------------
-- Reduction trees --
---------------------

-- Synonym for contractions of the form \i/ j <- p
type Contraction = (Int, Int, SBool String)

-- Gets all depth-1 contractions
allContractions :: PathState -> [Contraction]
allContractions ps@(PathState paths pp st)
  | pp == 0   = []
  | otherwise = do
      v        <- paths \\ (map unvar $ Set.toList $ Set.unions $ map vars st)
      eqn      <- maybeToList . toBooleanPoly . P.quotVar (var v) $ pp
      (u, sub) <- take 1 . filter (\(u, sub) -> unvar u `elem` paths) $ solveForX eqn
      return (v, unvar u, sub)

-- Applies a contraction
applyContraction :: PathState -> Contraction -> PathState
applyContraction ps (v, u, sub) = PathState pvars' pp' st' where
  pvars' = pvars ps \\ [v,u]
  pp'    = P.subst (var u) sub . remVar (var v) $ pp ps
  st'    = map (P.subst (var u) sub) $ st ps

-- Generalizes a contraction to an equation
generalize :: Contraction -> SBool String
generalize (_, u, sub) = ofVar (var u) + sub

-- Groups non-conflicting contractions
groupContractions :: [Contraction] -> [[Contraction]]
groupContractions []     = []
groupContractions (x:xs) = part:groupContractions xs' where
  (part,xs')     = foldr f ([x],[]) xs
  f x (part, xs) = case all (check x) part of
    True -> (x:part,xs)
    False -> (part,x:xs)
  check (v,u,_) (v',u',_) = intersect [v,u] [v',u'] == []

-- Pretty prints a reduction tree
ppReductionTree :: PathState -> [String]
ppReductionTree = go "" Nothing where
  go pref con ps = pref:root:subtrees where
    root = case con of
      Nothing  -> pref ++ "--" ++ show ps
      Just con -> pref ++ "--(" ++ show con ++ ")" ++ show ps
    subtrees = concatMap f $ allContractions ps where
      f con = go (pref ++ "    |") (Just con) $ applyContraction ps con

-- Collects all equations in the reduction tree
-- Most general
generateEquations :: PathState -> [SBool String]
generateEquations = nub . go where
  go ps =
    let eqns = allContractions ps in
      (map generalize eqns) ++ concatMap (go . applyContraction ps) eqns

-- Memoized over intermediary path states
-- High memory usage
generateEquationsMemo :: PathState -> [SBool String]
generateEquationsMemo = snd . go Set.empty where
  go seen ps
    | Set.member ps seen = (seen, [])
    | otherwise          = (Set.insert ps seen', eqns') where
        eqns'            = nub (map generalize eqns) ++ subtree
        eqns             = allContractions ps
        (seen', subtree) = foldr g (seen, []) eqns
        g con (seen, xs) =
          let (seen', eqs) = go seen (applyContraction ps con) in
            (seen', eqs ++ xs)

-- Groups into independent contractions and applies each set together
-- Doesn't get all contractions
generateEquationsGrouped :: PathState -> [SBool String]
generateEquationsGrouped = nub . go where
  go ps =
    let eqns = allContractions ps
        grps = groupContractions eqns
        go'  = go . foldr (flip applyContraction) ps
    in
      (map generalize eqns) ++ concatMap go' grps

-- Groups into independent contractions and applies one representative from each set
-- Not great
generateEquationsDirected :: PathState -> [SBool String]
generateEquationsDirected = nub . go where
  go ps =
    let eqns = allContractions ps
        grps = groupContractions eqns
    in
      (map generalize eqns) ++ concatMap (go . applyContraction ps . head) grps

-- Fixed tree depth
generateEquationsFixed :: Int -> PathState -> [SBool String]
generateEquationsFixed k = nub . go k where
  go k ps =
    let eqns = allContractions ps in
      if k <= 0 then
        (map generalize eqns) ++ concatMap (go k . applyContraction ps) (take 1 eqns)
      else
        (map generalize eqns) ++ concatMap (go (k-1) . applyContraction ps) eqns

-- Randomizes the search. Uses unsafe IO
generateEquationsRandom :: PathState -> [SBool String]
generateEquationsRandom ps = nub $ unsafePerformIO (fmap (go ps) $ getStdGen) where
  go ps gen = case allContractions ps of
    [] -> []
    xs ->
      let eqns      = allContractions ps
          (i, gen') = randomR (0, length eqns - 1) gen
      in
        (map generalize eqns) ++ go (applyContraction ps $ eqns!!i) gen'

-- Computes a matrix for a list of affine parities
matrixify :: [(F2Vec, Bool)] -> State Ctx F2Mat
matrixify bvs = gets dim >>= return . fromList . go where
  go n = map (\(b,p) -> (fromBool p)#(zeroExtend (n - width b) b)) bvs

-- Computes a list of affine parities from a matrix
unmatrixify :: F2Mat -> State Ctx [(F2Vec, Bool)]
unmatrixify mat = gets dim >>= go where
  go n = return . map (\bv -> (zeroExtend (-1) bv, bv@.n)) $ toList mat

-- Get a substitution for each bitvector equation
getSubs :: [(F2Vec, Bool)] -> [(Int, (F2Vec, Bool))]
getSubs eqns = do
  (bv, parity) <- eqns
  if (bv == 0)
    then []
    else let v = lsb1 bv in return (v, (bv `xor` (bit v), parity))

-- Gets a list of canonical substitutions
canonicalSubs :: [SBool String] -> State Ctx [(Int, (F2Vec, Bool))]
canonicalSubs eqns = do
  bvs <- mapM linearize eqns
  mat <- matrixify bvs
  bvs' <- unmatrixify . fst . runWriter $ toEchelon mat
  return $ getSubs bvs

-- Finding [HH] reductions
applyReductions :: State Ctx ()
applyReductions = do
  paths    <- gets $ Map.keys . quad
  poly     <- gets computePP
  state    <- gets $ map toPolynomial . Map.elems . ket
  let eqns = concat [generateEquationsRandom $ PathState paths poly state | i <- [0..5]]
  subs     <- canonicalSubs . nub . filter ((1 >=) . degree) $ eqns
  mapM_ (\(v, sub) -> substVar v sub) subs
  return ()

----------------------------------------------------------------------
{- The algorithm proper -}

-- Generates an initial state
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = st where
  st  = Ctx dim (Map.fromList ket) Map.empty Map.empty 0
  dim = length inputs
  ket = zip (inputs ++ (vars\\inputs)) [(bitI dim x, False) | x <- [0..]]

-- Applies the algorithm
algorithm :: [Primitive] -> State Ctx ()
algorithm circ = applyCircuit circ >> applyReductions

-- The phase folding algorithm
equationFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
equationFold vars inputs circ =
  let result = execState (algorithm circ) $ initialState vars inputs
      phases = Map.elems $ terms result
      (map, gphase) = foldr go (Map.empty, phase result) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, False) -> (l, gphase, angle)
                (l, True)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if l == loc then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
      circ' = concatMap go (zip circ [2..]) where
        go (gate, l) = case Map.lookup l map of
              Nothing -> [(gate, l)]
              Just angle
                | angle == 0 -> []
                | otherwise -> zip (synthesizePhase (getTarget gate) angle) [0..]
        getTarget gate = case gate of
          T x    -> x
          S x    -> x
          Z x    -> x
          Tinv x -> x
          Sinv x -> x
          Rz _ x -> x
  in
    (fst $ unzip $ circ') ++ (globalPhase (head vars) gphase)
