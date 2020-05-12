module Feynman.Optimization.StateFold where

import Data.List hiding (transpose)
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Data.Bits

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial as P
import Feynman.Synthesis.Phase

{-- "State" folding optimization -}
{- The idea here is to apply some [HH] reductions when possible
   to help find extra T reductions. Allows identification of
   some compute-uncompute patterns and basis changes without
   losing too much efficiency -}

data Ctx = Ctx {
  dim   :: Int,
  ket   :: Map ID (F2Vec, Bool),
  terms :: Map F2Vec (Set (Loc, Bool), Angle),
  phase :: Angle,
  pp    :: Multilinear Angle,
  paths :: Set Int
} deriving Show

-- The /i/th variable
var :: Int -> String
var i = "v" ++ show i

-- The number of a variable
unvar :: String -> Int
unvar = read . tail

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
    False -> st { terms = Map.alter (add theta) bv (terms st),
                  pp    = pp st + distribute theta (multilinearOfBV (bv, False)) }
    True  -> st { terms = Map.alter (add (-theta)) bv (terms st),
                  pp    = pp st + distribute theta (multilinearOfBV (bv, True)),
                  phase = (phase st) + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, parity), theta)

-- Adds a quadratic phase term
addQuadTerm :: Int -> (F2Vec, Bool) -> State Ctx ()
addQuadTerm n bv = modify $ \st -> st { pp = pp st + ofVar (var n) * quad } where
  quad = distribute (Discrete $ dyadic 1 1) (multilinearOfBV bv)

-- Finding [HH] reductions
applyReductions :: State Ctx ()
applyReductions = do
  poly     <- gets pp
  pathVars <- gets paths
  outVars  <- gets (Set.unions . map (varsOfBV . fst) . Map.elems . ket)
  case matchHHLinear poly $ Set.difference pathVars outVars of
    Nothing         -> return ()
    Just (x, y, bv) -> do
      elimVar x
      substVar y bv
      applyReductions

-- Remove an internal variable
elimVar :: Int -> State Ctx ()
elimVar x = modify $ \st -> st { terms = Map.filterWithKey f $ terms st,
                                 pp    = removeVar (var x) $ pp st }
  where f parity _ = Set.notMember x $ varsOfBV parity

-- Substitute a variable
substVar :: Int -> (F2Vec, Bool) -> State Ctx ()
substVar x bv = modify go where
  go st = st { terms = Map.mapKeysWith add substKey $ terms st,
               pp    = P.subst (var x) (multilinearOfBV bv) $ pp st,
               ket   = Map.map substState $ ket st }
  add (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)
  substKey bv' = case testBit bv' x of
    False -> bv'
    True  -> (complementBit bv' x) + (fst bv)
  substState bv = (substKey $ fst bv, snd bv)

{- Utilities -}

injectZ2 :: Periodic a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing

toBooleanPoly :: (Eq a, Periodic a) => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2 . simplify

-- Converts a bitvector into a polynomial
multilinearOfBV :: (F2Vec, Bool) -> Multilinear Bool
multilinearOfBV bv = Set.foldr (+) const . Set.map (ofVar . var) . varsOfBV $ fst bv
  where const = if snd bv then 1 else 0

-- Gets the variables in a bitvector
varsOfBV :: F2Vec -> Set Int
varsOfBV bv = Set.fromList $ filter (testBit bv) [0..(width bv) - 1]

-- Converts a linear Boolean polynomial into a bitvector
bvOfMultilinear :: Multilinear Bool -> Maybe (F2Vec, Bool)
bvOfMultilinear p
  | degree p > 1 = Nothing
  | otherwise    = Just $ unsafeConvert p
    where unsafeConvert = (foldl' f (bitI 0 0, False)). Map.toList . P.terms
          f (bv, const) (m, b)
            | b == False      = (bv, const)
            | emptyMonomial m = (bv, const `xor` True)
            | otherwise       =
              let v = unvar $ firstVar m in
                (bv `xor` (bitI (v+1) v), const)

-- Matches a *linear* instance of [HH]
matchHHLinear :: Multilinear Angle -> Set Int -> Maybe (Int, Int, (F2Vec, Bool))
matchHHLinear poly paths = msum . map (go . var) $ Set.toDescList paths where
  go v = do
    p'       <- toBooleanPoly $ factorOut v poly
    (u, sub) <- find validSoln $ solveForX p'
    bv       <- bvOfMultilinear sub
    return (unvar v, unvar u, bv)
  validSoln (u, sub) = (unvar u) `elem` paths && degree sub <= 1

{- The Super phase folding analysis -}
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
    modify $ \st -> st { paths = Set.insert n $ paths st }
    addQuadTerm n bv
    setSt v (bit n, False)
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _      -> error "Unsupported gate"

{- Run the analysis on a circuit and state -}
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState go where
  go = mapM_ applyGate (zip circ [2..]) >> applyReductions

{- Generates an initial state -}
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty 0 0 Set.empty where
  dim = length inputs
  ket = zip (inputs ++ (vars \\ inputs)) [(bitI dim x, False) | x <- [0..]]
  
stateFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
stateFold vars inputs circ =
  let result = runCircuit circ $ initialState vars inputs
      (lmap, phase') =
        let f (lmap, phase) (locs, exp) =
              let (i, phase', exp') = case Set.findMin locs of
                    (i, False) -> (i, phase, exp)
                    (i, True)  -> (i, phase + exp, (-exp))
              in
                (Set.foldr (\(j, _) -> Map.insert j (if i == j then exp' else zero)) lmap locs, phase')
        in
          foldl' f (Map.empty, phase result) (Map.elems $ terms result)
      circ' =
        let getTarget gate = case gate of
              T x    -> x
              S x    -> x
              Z x    -> x
              Tinv x -> x
              Sinv x -> x
              Rz _ x -> x
            f (gate, i) = case Map.lookup i lmap of
              Nothing -> [(gate, i)]
              Just exp
                | exp == zero -> []
                | otherwise   -> zip (synthesizePhase (getTarget gate) exp) (repeat i)
        in
          concatMap f (zip circ [2..])
  in
    (fst $ unzip $ circ') ++ (globalPhase (head vars) phase')

  
