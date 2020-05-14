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
  ket   :: Map ID (Multilinear Bool),
  terms :: Map (Multilinear Bool) (Set (Loc, Bool), Angle),
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
getSt :: ID -> State Ctx (Multilinear Bool)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bexp -> return bexp
    Nothing -> do
      n <- alloc
      let bexp = ofVar $ var n
      setSt v bexp
      return bexp

-- Set the state of a variable
setSt :: ID -> Multilinear Bool -> State Ctx ()
setSt v bexp = modify $ \st -> st { ket = Map.insert v (simplify bexp) (ket st) }

-- Adds a mergeable phase term
addTerm :: Angle -> Loc -> Multilinear Bool -> State Ctx ()
addTerm theta loc bexp = modify go where
  go st = st { terms = Map.alter (add theta') bexp' (terms st),
               pp    = simplify $ pp st + distribute theta bexp,
               phase = phase st + (if parity then theta else 0) }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, parity), theta)
  parity = getConstant bexp
  theta' = if parity then (-theta) else theta
  bexp'  = simplify . dropConstant $ bexp

-- Adds a quadratic phase term
addQuadTerm :: Int -> Multilinear Bool -> State Ctx ()
addQuadTerm n bexp = modify $ \st -> st { pp = simplify $ pp st + poly } where
  poly = distribute (Discrete $ dyadic 1 1) $ ofVar (var n) * bexp

-- Finding [HH] reductions
applyReductions :: Int -> State Ctx ()
applyReductions cutoff = do
  poly     <- gets pp
  pathVars <- gets paths
  outVars  <- gets (Set.fromList . map unvar . concatMap vars . Map.elems . ket)
  case matchHH poly (Set.difference pathVars outVars) pathVars cutoff of
    Nothing         -> return ()
    Just (x, y, bexp) -> do
      elimVar x
      substVar y bexp
      applyReductions cutoff

-- Remove an internal variable
elimVar :: Int -> State Ctx ()
elimVar x = modify $ \st -> st { pp = simplify . removeVar (var x) $ pp st }

-- Substitute a variable
substVar :: Int -> Multilinear Bool -> State Ctx ()
substVar x bexp = modify go where
  go st = st { terms = Map.mapKeysWith c f $ terms st,
               pp    = simplify . P.subst (var x) bexp $ pp st,
               ket   = Map.map (simplify . P.subst (var x) bexp) $ ket st }
  f = simplify . dropConstant . P.subst (var x) bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

{- Utilities -}

injectZ2 :: Periodic a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing

toBooleanPoly :: (Eq a, Periodic a) => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2

-- Matches a instance of [HH]
matchHH :: Multilinear Angle -> Set Int -> Set Int -> Int -> Maybe (Int, Int, Multilinear Bool)
matchHH pp cand paths cutoff = msum . map (go . var) $ Set.toDescList cand where
  go v = do
    pp'      <- toBooleanPoly . factorOut v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (unvar v, unvar u, sub)
  validSoln (u, sub) = Set.member (unvar u) paths && degree sub <= cutoff

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
    bexp  <- getSt c
    bexp' <- getSt t
    setSt t (bexp + bexp')
  X v -> do
    bexp <- getSt v
    setSt v (1 + bexp)
  H v -> do
    bexp <- getSt v
    n <- alloc
    modify $ \st -> st { paths = Set.insert n $ paths st }
    addQuadTerm n bexp
    setSt v (ofVar $ var n)
  Swap u v -> do
    bexp  <- getSt u
    bexp' <- getSt v
    setSt u bexp'
    setSt v bexp
  _      -> error "Unsupported gate"

{- Run the analysis on a circuit and state -}
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState $ do
  mapM_ applyGate (zip circ [2..])
  applyReductions 1 -- linear reductions
  applyReductions 2 -- quadratic reductions

{- Generates an initial state -}
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = st where
  st  = Ctx dim (Map.fromList ket) Map.empty 0 0 Set.empty
  dim = length inputs
  ket = (zip inputs [ofVar (var x) | x <- [0..]]) ++ (zip (vars\\inputs) $ repeat 0)
  
stateFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
stateFold vars inputs circ =
  let result = runCircuit circ $ initialState vars inputs
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
