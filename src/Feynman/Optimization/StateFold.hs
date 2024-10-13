module Feynman.Optimization.StateFold where

import Data.List hiding (transpose)
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Data.Bits

import System.IO.Unsafe
import System.Random

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial (degree)
import Feynman.Algebra.Polynomial.Multilinear hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial.Multilinear as P
import Feynman.Algebra.Polynomial.Multilinear.Groebner
import Feynman.Algebra.Pathsum.Balanced (toBooleanPoly)
import Feynman.Synthesis.Phase
import Feynman.Optimization.Clifford

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

-- Adds a non-mergeable phase term
addTermNM :: Angle -> SBool String -> State Ctx ()
addTermNM theta bexp = modify $ \st -> st { pp = pp st + poly } where
  poly = distribute theta bexp

-- Adds a quadratic phase term
addQuadTerm :: SBool String -> SBool String -> State Ctx ()
addQuadTerm bexp bexp' = modify $ \st -> st { pp = pp st + poly } where
  poly = P.lift $ bexp * bexp'

-- Finding [HH] reductions
applyReductions :: Maybe Int -> State Ctx [SBool String]
applyReductions cutoff = do
  poly     <- gets pp
  pathVars <- gets paths
  outVars  <- gets (Set.unions . map (Set.map unvar . vars) . Map.elems . ket)
  let ideal = matchI poly (Set.difference pathVars outVars) pathVars cutoff
  let hhIst = matchHH poly (Set.difference pathVars outVars) pathVars cutoff
  let omIst = matchOmega poly (Set.difference pathVars outVars) pathVars
  case (hhIst, omIst) of
    (Just (x, y, bexp), _) -> do
      elimVar x
      substVar y bexp
      xs <- applyReductions cutoff
      return $ ((ofVar (var y) + bexp):xs) ++ ideal
    (Nothing, Just (x, bexp)) -> do
      elimVar x
      let poly = constant (Discrete $ fromDyadic $ dyadic 1 2) + distribute (Discrete $ fromDyadic $ dyadic 3 1) (P.lift bexp)
      modify (\st -> st { pp = pp st + poly })
      xs <- applyReductions cutoff
      return $ xs ++ ideal
    (Nothing, Nothing)     -> return ideal

-- Remove an internal variable
elimVar :: Int -> State Ctx ()
elimVar x = modify $ \st -> st { pp = remVar (var x) $ pp st }

-- Substitute a variable
substVar :: Int -> SBool String -> State Ctx ()
substVar x bexp = modify go where
  go st = st { terms = applyToPP $ terms st,
               pp    = P.subst (var x) bexp $ pp st,
               ket   = Map.map (P.subst (var x) bexp) $ ket st }
  applyToPP terms =
    let (xterms, nxterms) = Map.partitionWithKey (\m _ -> Set.member (var x) $ vars m) terms
        xterms'  =
          if getConstant bexp == 1
          then Map.map (\(s, a) -> (Set.map (\(l,p) -> (l, 1 + p)) s, -a)) xterms
          else xterms
        xterms'' = Map.mapKeysWith c f $ xterms'
    in
      Map.unionWith c xterms'' nxterms
  f = dropConstant . P.subst (var x) bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

-- Matches a instance of [I]
matchI :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe Int -> [SBool String]
matchI pp cand paths cutoff = filter isValid . catMaybes . map (go . var) $ Set.toAscList cand where
  go v = toBooleanPoly . quotVar v $ pp
  isValid pp = case cutoff of
    Just d  -> degree pp <= d
    Nothing -> True

-- Matches a instance of [HH]
matchHH :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe Int -> Maybe (Int, Int, SBool String)
matchHH pp cand paths cutoff = msum . map (go . var) $ Set.toAscList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (unvar v, unvar u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && Set.member (unvar u) paths
    Nothing -> Set.member (unvar u) paths

-- Matches an instance of the [omega] rule
matchOmega :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe (Int, SBool String)
matchOmega pp cand paths = msum . map (go . var) $ Set.toAscList cand where
  go v = do
    pp' <- toBooleanPoly . addFactor v $ pp
    return (unvar v, pp')
  addFactor v p = constant (Discrete $ fromDyadic $ dyadic 3 1) + quotVar v p

-- Matches a random instance of [HH]
matchRandomHH :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe Int -> Maybe (Int, Int, SBool String)
matchRandomHH pp cand paths cutoff = pickRandom . catMaybes . map (go . var) $ Set.toDescList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (unvar v, unvar u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && Set.member (unvar u) paths
    Nothing -> Set.member (unvar u) paths
  pickRandom [] = Nothing
  pickRandom xs = Just $ xs!!(fst $ randomR (0, length xs - 1) (unsafePerformIO $ getStdGen))

-- Reduce with respect to a groebner basis for a set of polynomials
reduceAll :: [SBool String] -> State Ctx ()
reduceAll ideal = do
  st <- get
  let gbasis = rbuchberger ideal
  let comb (s,a) (t,b) = (Set.union s t, a + b)
  put $ st { terms = Map.mapKeysWith comb (flip mvd gbasis) $ terms st }

{- The Super phase folding analysis -}
applyGate :: Bool -> (Primitive, Loc) -> State Ctx ()
applyGate tonly (gate, l) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) l
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) l
  S v    -> getSt v >>= if tonly then addTermNM (dyadicPhase $ dyadic 1 1) else addTerm (dyadicPhase $ dyadic 1 1) l
  Sinv v -> getSt v >>= if tonly then addTermNM (dyadicPhase $ dyadic 3 1) else addTerm (dyadicPhase $ dyadic 3 1) l
  Z v    -> getSt v >>= if tonly then addTermNM (dyadicPhase $ dyadic 1 0) else addTerm (dyadicPhase $ dyadic 1 0) l
  Rz p v -> getSt v >>= addTerm p l
  CNOT c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    setSt t (bexp + bexp')
  CZ c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    addQuadTerm bexp bexp'
  X v -> do
    bexp <- getSt v
    setSt v (1 + bexp)
  H v -> do
    bexp <- getSt v
    n <- alloc
    modify $ \st -> st { paths = Set.insert n $ paths st }
    addQuadTerm (ofVar $ var n) bexp
    setSt v (ofVar $ var n)
  Swap u v -> do
    bexp  <- getSt u
    bexp' <- getSt v
    setSt u bexp'
    setSt v bexp
  _      -> error $ "Unsupported gate " ++ show gate

{- Run the analysis on a circuit and state -}
runCircuit :: Bool -> Int -> [AnnotatedPrimitive] -> Ctx -> Ctx
runCircuit tonly d circ = execState $ (mapM_ (applyGate tonly) circ) >> go where
  go | d == 1 = do
         i1 <- applyReductions (Just 1) -- linear reductions
         return ()
     | d > 1  = do
         i1 <- applyReductions (Just 1) -- linear reductions
         id <- applyReductions (Just d) -- reductions up to degree d
         return ()
     | d < 1  = do
         i1 <- applyReductions (Just 1) -- linear reductions
         id <- applyReductions Nothing  -- all reductions
         reduceAll $ i1 ++ id
         return ()

{- Generates an initial state -}
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = st where
  st  = Ctx dim (Map.fromList ket) Map.empty 0 0 Set.empty
  dim = length inputs
  ket = (zip inputs [ofVar (var x) | x <- [0..]]) ++ (zip (vars\\inputs) $ repeat 0)
  
stateFold :: Int -> [ID] -> [ID] -> [Primitive] -> [Primitive]
stateFold d vars inputs circ = fst . unzip $ stateFold' d vars inputs (annotate circ)

stateFold' :: Int -> [ID] -> [ID] -> [AnnotatedPrimitive] -> [AnnotatedPrimitive]
stateFold' d vars inputs circ =
  let result = runCircuit False d circ $ initialState vars inputs
      phases = Map.elems $ terms result
      (map, gphase) = foldr go (Map.empty, phase result) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, 0) -> (l, gphase, angle)
                (l, 1)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if l == loc then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
      circ' = concatMap go circ where
        go (gate, l) = case Map.lookup l map of
              Nothing -> [(gate, l)]
              Just angle
                | angle == 0 -> []
                | otherwise -> annotateWith l (synthesizePhase (getTarget gate) angle)
        getTarget gate = case gate of
          T x    -> x
          S x    -> x
          Z x    -> x
          Tinv x -> x
          Sinv x -> x
          Rz _ x -> x
  in
    circ' ++ (annotateWith (-1) $ globalPhase (head vars) gphase)

-- Fold after swapping CNOT to CZ
pauliFold :: Int -> [ID] -> [ID] -> [Primitive] -> [Primitive]
pauliFold d vars inputs circ = 
  let initCirc = zip circ [2..]
      tmpCirc  = simplifyCliffords' . simplifyPrimitive' . expandCNOT' $ initCirc
      result = runCircuit True d tmpCirc $ initialState vars inputs
      phases = Map.elems $ terms result
      (map, gphase) = foldr go (Map.empty, phase result) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, 0) -> (l, gphase, angle)
                (l, 1)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if l == loc then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
      circ' = concatMap go initCirc where
        go (gate, l) = case Map.lookup l map of
              Nothing -> [(gate, l)]
              Just angle
                | angle == 0 -> []
                | otherwise -> annotateWith l (synthesizePhase (getTarget gate) angle)
        getTarget gate = case gate of
          T x    -> x
          S x    -> x
          Z x    -> x
          Tinv x -> x
          Sinv x -> x
          Rz _ x -> x
  in
    (fst . unzip $ circ') ++ (globalPhase (head vars) gphase)
