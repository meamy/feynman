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
import Feynman.Algebra.Polynomial (degree)
import Feynman.Algebra.Polynomial.Multilinear hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial.Multilinear as P
import Feynman.Algebra.Pathsum.Balanced (toBooleanPoly)
import Feynman.Synthesis.Phase

{-- "State" folding optimization -}
{- The idea here is to apply some [HH] reductions when possible
   to help find extra T reductions. Allows identification of
   some compute-uncompute patterns and basis changes without
   losing too much efficiency -}

data Ctx = Ctx {
  dim   :: Int,
  ket   :: Map ID (SBool String),
  terms :: Map (SBool String) (Set (Loc, FF2), Angle),
  phase :: Angle,
  pp    :: PseudoBoolean String Angle,
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
getSt :: ID -> State Ctx (SBool String)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bexp -> return bexp
    Nothing -> do
      n <- alloc
      let bexp = ofVar $ var n
      setSt v bexp
      return bexp

-- Set the state of a variable
setSt :: ID -> SBool String -> State Ctx ()
setSt v bexp = modify $ \st -> st { ket = Map.insert v bexp (ket st) }

-- Adds a mergeable phase term
addTerm :: Angle -> Loc -> SBool String -> State Ctx ()
addTerm theta loc bexp = modify go where
  go st = st { terms = Map.alter (add theta') bexp' (terms st),
               pp    = pp st + distribute theta bexp,
               phase = phase st + (if parity == 1 then theta else 0) }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, parity), theta)
  parity = getConstant bexp
  theta' = if parity == 1 then (-theta) else theta
  bexp'  = dropConstant $ bexp

-- Adds a quadratic phase term
addQuadTerm :: Int -> SBool String -> State Ctx ()
addQuadTerm n bexp = modify $ \st -> st { pp = pp st + poly } where
  poly = P.lift $ ofVar (var n) * bexp

-- Finding [HH] reductions
applyReductions :: Maybe Int -> State Ctx ()
applyReductions cutoff = do
  poly     <- gets pp
  pathVars <- gets paths
  outVars  <- gets (Set.unions . map (Set.map unvar . vars) . Map.elems . ket)
  case matchHH poly (Set.difference pathVars outVars) pathVars cutoff of
    Nothing         -> return ()
    Just (x, y, bexp) -> do
      elimVar x
      substVar y bexp
      applyReductions cutoff

-- Remove an internal variable
elimVar :: Int -> State Ctx ()
elimVar x = modify $ \st -> st { pp = remVar (var x) $ pp st }

-- Substitute a variable
substVar :: Int -> SBool String -> State Ctx ()
substVar x bexp = modify go where
  go st = st { terms = Map.mapKeysWith c f $ terms st,
               pp    = P.subst (var x) bexp $ pp st,
               ket   = Map.map (P.subst (var x) bexp) $ ket st }
  f = dropConstant . P.subst (var x) bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

-- Matches a instance of [HH]
matchHH :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe Int -> Maybe (Int, Int, SBool String)
matchHH pp cand paths cutoff = msum . map (go . var) $ Set.toDescList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (unvar v, unvar u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && Set.member (unvar u) paths
    Nothing -> Set.member (unvar u) paths

{- The Super phase folding analysis -}
applyGate :: (Primitive, Loc) -> State Ctx ()
applyGate (gate, l) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) l
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) l
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) l
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) l
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) l
  Rz p v -> getSt v >>= addTerm p l
  CNOT c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    setSt t (bexp + bexp')
  CZ c t -> return () -- no-op for phase folding
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
  _      -> error $ "Unsupported gate " ++ show gate

{- Run the analysis on a circuit and state -}
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState $ do
  mapM_ applyGate (zip circ [2..])
  applyReductions (Just 1) -- linear reductions
  applyReductions (Just 2) -- quadratic reductions
  applyReductions Nothing -- all other reductions

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
                (l, 0) -> (l, gphase, angle)
                (l, 1)  -> (l, gphase + angle, (-angle))
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
