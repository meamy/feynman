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

import Debug.Trace

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial as P
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
  T v    -> getSt v >>= addTerm (Discrete $ dyadic 1 3) l
  Tinv v -> getSt v >>= addTerm (Discrete $ dyadic 7 3) l
  S v    -> getSt v >>= addTerm (Discrete $ dyadic 1 2) l
  Sinv v -> getSt v >>= addTerm (Discrete $ dyadic 3 2) l
  Z v    -> getSt v >>= addTerm (Discrete $ dyadic 1 1) l
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
computePP :: Ctx -> Multilinear Angle
computePP st = simplify $ foldl' (+) (constant $ phase st) $ l ++ q where
  l = map go . Map.toList $ terms st where
    go (bv, (_,theta)) = distribute theta (toPolynomial (bv, False))
  q = map go . Map.toList $ quad st where
    go (n, v) = distribute (Discrete $ dyadic 1 1) poly where
      poly = ofVar (var n) * toPolynomial v

-- Converts a bitvector into a polynomial
toPolynomial :: (F2Vec, Bool) -> Multilinear Bool
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
linearize :: Multilinear Bool -> State Ctx (F2Vec, Bool)
linearize = foldM go (bitI 0 0, False) . Map.keys . P.terms where
  go (bv, parity) mono
    | monomialDegree mono == 0 = return (bv, parity `xor` True)
    | monomialDegree mono == 1 = do
        let v = unvar $ firstVar mono
        return (bv `xor` (bit v), parity)
    | otherwise = do
        n <- alloc
        return (bv `xor` (bit n), parity)

injectZ2 :: Periodic a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing

toBooleanPoly :: (Eq a, Periodic a) => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2

-- Gets the variables in a bitvector
varsOfBV :: F2Vec -> [Int]
varsOfBV bv = Set.toList . Set.fromList $ filter (testBit bv) [0..(width bv) - 1]

-- Converts a linear Boolean polynomial into a bitvector
fromPolynomial :: Multilinear Bool -> Maybe (F2Vec, Bool)
fromPolynomial p
  | degree p > 1 = Nothing
  | otherwise    = Just $ unsafeConvert p
    where unsafeConvert = (foldl' f (bitI 0 0, False)). Map.toList . P.terms
          f (bv, const) (m, b)
            | b == False      = (bv, const)
            | emptyMonomial m = (bv, const `xor` True)
            | otherwise       =
              let v = unvar $ firstVar m in
                (bv `xor` (bitI (v+1) v), const)

-- Lazily generates a tree of equations
generateEquations :: Multilinear Angle -> [Int] -> [Multilinear Bool]
generateEquations poly cand
  | poly == 0 = []
  | otherwise = do
      v        <- cand
      eqn      <- maybeToList . toBooleanPoly . factorOut (var v) $ poly
      trace ("(" ++ show poly ++ "): found equality " ++ show eqn ++ " = 0") $ return ()
      (u, sub) <- maybeToList $ find (\(u, sub) -> True) $ solveForX eqn
      let poly' = simplify . P.subst u sub . removeVar (var v) $ poly
      let deps  = if elem (unvar u) cand then [] else map unvar $ vars sub
      eqn:(generateEquations poly' (cand \\ (v:deps)))

-- Cycle detecting version
reachableEqns :: Multilinear Angle -> [Int] -> [Multilinear Bool]
reachableEqns = go [] where
  go acc poly cand
    | poly == 0 = acc
    | otherwise =
      let expand v acc = fromMaybe acc $ do
            eqn <- toBooleanPoly $ factorOut (var v) poly
            guard $ (not (eqn == 0) && not (elem eqn acc))
            (u, sub) <- find (\_ -> True) $ solveForX eqn
            let poly' = simplify . P.subst u sub . removeVar (var v) $ poly
            let deps  = if elem (unvar u) cand then [] else map unvar $ vars sub
            return $ go (eqn:acc) poly' (cand \\ (v:deps))
      in
        foldr expand acc cand

-- Only contracts on each candidate once
reachableEqns' :: Multilinear Angle -> [Int] -> [Multilinear Bool]
reachableEqns' poly cand = go ([], cand) [(poly, cand)] where
  go (acc, []) _      = acc
  go (acc, xs) []     = acc
  go (acc, xs) (p:ps)
    | fst p == 0      = go (acc, xs) ps
    | otherwise       =
      let matches = do
            v       <- intersect xs (snd p)
            eqn     <- maybeToList . toBooleanPoly . factorOut (var v) $ fst p
            guard   $ (not (eqn == 0) && not (elem eqn acc))
            (u,sub) <- take 1 $ solveForX eqn
            let p'  = simplify . P.subst u sub . removeVar (var v) $ fst p
            let dps = if elem (unvar u) (snd p) then [] else map unvar $ vars sub
            return (eqn, v, (p',(snd p)\\(v:dps)))
      in
        case matches of
          [] -> go (acc, xs) ps
          ((eqn,x,p'):_) -> go (eqn:acc, xs\\[x]) (p':p:ps)

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
canonicalSubs :: [Multilinear Bool] -> State Ctx [(Int, (F2Vec, Bool))]
canonicalSubs eqns = do
  bvs <- mapM linearize eqns
  mat <- matrixify bvs
  bvs' <- unmatrixify . fst . runWriter $ toEchelon mat
  return $ getSubs bvs

-- Finding [HH] reductions
applyReductions :: State Ctx ()
applyReductions = do
  poly    <- gets computePP
  paths   <- gets $ Map.keys . quad
  outVars <- gets $ concatMap (varsOfBV . fst) . Map.elems . ket
  cand    <- gets $ \st -> paths \\ outVars
  let eqns = nub . filter ((1 >=) . degree) $ reachableEqns poly cand
  trace ("Generated equations: " ++ show eqns) $ return ()
  subs    <- canonicalSubs eqns
  trace ("Canonicalized equations: " ++ show subs) $ return ()
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
