{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : RelationalFoldNL
Description : Non-linear relational phase folding optimization
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

-}

module Feynman.Optimization.RelationalFoldNL where

import Data.List hiding (transpose)
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict hiding (join)
import Data.Bits
import Data.Coerce (coerce)
import Data.String (IsString(..))

import Feynman.Core
import qualified Feynman.Util.Unicode as U
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial (degree)
import Feynman.Algebra.Polynomial.Multilinear hiding (zero, one, terms)
import qualified Feynman.Algebra.Polynomial.Multilinear as P
import Feynman.Algebra.Polynomial.Multilinear.Groebner
import Feynman.Algebra.Pathsum.Balanced (toBooleanPoly)
import Feynman.Synthesis.Phase

import qualified Debug.Trace as Trace

{-----------------------------------
 Utilities
 -----------------------------------}

-- | Terms of the phase polynomial
type Term = (Set (Loc, FF2), Angle)

-- | The type of variables
data Var = Init Int | Prime Int | Temp Int deriving (Eq)

-- | Ordered right to left
instance Ord Var where
  compare a b = case (a, b) of
    (Temp i, Temp j)   -> compare i j
    (Temp i, _)        -> GT
    (_, Temp j)        -> LT
    (Prime i, Prime j) -> compare i j
    (Prime i, _)       -> GT
    (_, Prime j)       -> LT
    (Init i, Init j)   -> compare i j

-- | Default elimination order
instance Elim Var where
  eliminate (Temp _) = True
  eliminate _        = False

-- | Use elimination order right off the bat
instance Ord (P.PowerProduct Var) where
  compare = lexdegOrd

instance Show Var where
  show (Init i)  = "x" ++ (U.subscript $ toInteger i)
  show (Prime i) = "x" ++ (U.subscript $ toInteger i) ++ "'"
  show (Temp i)  = "y" ++ (U.subscript $ toInteger i)

instance IsString Var where
  fromString _ = Temp 10000000

-- | Checks whether the variable is a temporary (path variable)
isTemp :: Var -> Bool
isTemp (Temp _) = True
isTemp _        = False

-- | Shifts primes to temporaries (e.g. in a transition ideal)
shiftPrimes :: Maybe Int -> Var -> Var
shiftPrimes Nothing (Prime i)  = Temp i
shiftPrimes (Just j) (Prime i) = Temp (i+j)
shiftPrimes _ v                = v

-- | Shifts inits to temporaries (e.g. in a transition ideal)
shiftInits :: Maybe Int -> Var -> Var
shiftInits Nothing (Init i)  = Temp i
shiftInits (Just j) (Init i) = Temp (i+j)
shiftInits _ v               = v

-- | Transition ideals
type TransIdeal = [SBool Var]

{-----------------------------------
 Optimization algorithm
 -----------------------------------}

data Ctx = Ctx {
  nVars   :: Int,
  nTemps  :: Int,
  ket     :: Map ID (SBool Var),
  terms   :: Map (SBool Var) Term,
  phase   :: Angle,
  orphans :: [Term],
  pp      :: PseudoBoolean Var Angle,
  ideal   :: TransIdeal
} deriving Show

-- | Allocate a new variable
allocInit :: State Ctx Var
allocInit = do
  n <- gets nVars
  modify $ \st -> st { nVars = n + 1 }
  return $ Init n

-- | Allocate a new temporary variable
allocTemp :: State Ctx Var
allocTemp = do
  n <- gets nTemps
  modify $ \st -> st { nTemps = n + 1 }
  return $ Temp n

-- | Get the state of variable v
getSt :: ID -> State Ctx (SBool Var)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bexp -> return bexp
    Nothing -> do
      n <- allocInit
      let bexp = ofVar n
      setSt v bexp
      return bexp

-- | Set the state of a variable
setSt :: ID -> SBool Var -> State Ctx ()
setSt v bexp = modify $ \st -> st { ket = Map.insert v bexp (ket st) }

-- | Adds a mergeable phase term
addTerm :: Angle -> Loc -> SBool Var -> State Ctx ()
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

-- | Adds a quadratic phase term
addQuadTerm :: SBool Var -> SBool Var -> State Ctx ()
addQuadTerm bexp bexp' = modify $ \st -> st { pp = pp st + poly } where
  poly = P.lift $ bexp * bexp'

-- | Remove a variable
elimVar :: Var -> State Ctx ()
elimVar x = modify $ \st -> st { pp = remVar x $ pp st }

-- | Substitute a variable
substVar :: Var -> SBool Var -> State Ctx ()
substVar x bexp = modify go where
  go st = st { --terms = Map.mapKeysWith c f $ terms st,
               pp    = P.subst x bexp $ pp st,
               ket   = Map.map (P.subst x bexp) $ ket st }
  --f = dropConstant . P.subst x bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

-- | Matches a instance of [HH] with maximum degree /cutoff/
matchHH :: PseudoBoolean Var Angle -> Set Var -> Maybe Int -> Maybe (Var, Var, SBool Var)
matchHH pp cand cutoff = msum . map go $ Set.toDescList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (v, u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && isTemp u
    Nothing -> isTemp u

-- | Finding [HH] reductions
applyReductions :: Maybe Int -> State Ctx [SBool Var]
applyReductions cutoff = do
  poly     <- gets pp
  let temps = Set.filter (isTemp) $ vars poly
  exposed  <- gets (Set.filter (isTemp) . Set.unions . map vars . Map.elems . ket)
  case matchHH poly (Set.difference temps exposed) cutoff of
    Nothing           -> return []
    Just (x, y, bexp) -> do
      elimVar x
      substVar y bexp
      xs <- applyReductions cutoff
      return $ (ofVar y + bexp):xs

-- | Reduce with respect to a groebner basis for a set of polynomials
reduceTerms :: State Ctx ()
reduceTerms = do
  st <- get
  let comb (s,a) (t,b) = (Set.union s t, a + b)
  put $ st { terms = Map.mapKeysWith comb (flip mvd $ ideal st) $ terms st }

-- | Computes an ideal for the state
computeIdeal :: State Ctx ()
computeIdeal = do
  i1 <- applyReductions (Just 1) -- linear reductions
  i2 <- applyReductions (Just 2) -- quadratic reductions
  ik <- applyReductions Nothing -- all other reductions
  modify (\st -> st { ideal = foldl (\gb -> reduceBasis . addToBasis gb) (ideal st) $ i1 ++ i2 ++ ik })
  --reduceAll $ rbuchberger $ i1 ++ i2 ++ ik
  --return $ i1 ++ i2 ++ ik

-- | Abstract transformers for individual gates
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
  CZ c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    addQuadTerm bexp bexp'
  X v -> do
    bexp <- getSt v
    setSt v (1 + bexp)
  H v -> do
    bexp <- getSt v
    n <- allocTemp
    addQuadTerm (ofVar n) bexp
    setSt v (ofVar n)
  Swap u v -> do
    bexp  <- getSt u
    bexp' <- getSt v
    setSt u bexp'
    setSt v bexp
  _      -> error $ "Unsupported gate " ++ show gate

-- | The initial state
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx nVars 0 (Map.fromList ket) Map.empty 0 [] 0 [] where
  nVars = length inputs
  ket = (zip inputs [ofVar (Init x) | x <- [0..]]) ++ (zip (vars\\inputs) $ repeat 0)
  
-- | Apply the transformers for a list of gates and reduce the result
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState $ do
  mapM_ applyGate (zip circ [2..])
  i1 <- applyReductions (Just 1) -- linear reductions
  i2 <- applyReductions (Just 2) -- quadratic reductions
  ik <- applyReductions Nothing -- all other reductions
  --reduceAll $ rbuchberger $ i1 ++ i2 ++ ik
  return ()

-- | The optimization restricted to circuits
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

{-----------------------------------
 State folding of the quantum WHILE
 -----------------------------------}

-- | Apply the MVD algorithm with respect to a Boolean ideal I
--   inside a multilinear polynomial. That is, for every term
--   aX^i, reduce X^i mod I to get f_i and then lift f_i
mvdInPP :: PseudoBoolean Var Angle -> [SBool Var] -> PseudoBoolean Var Angle
mvdInPP p ideal = foldr (+) 0 $ map go (toTermList p) where
  go (a,m) = distribute a (mvd (ofMonomial m) ideal)

-- | Compose two transition ideals
compose :: TransIdeal -> TransIdeal -> TransIdeal
compose i j = eliminateAll $ idealPlus ishift jshift where
  ishift = map (rename $ shiftPrimes Nothing) i
  jshift = map (rename $ shiftInits Nothing) j

-- | Compute the join of two transition ideals (i.e. the join of their varieties)
join :: TransIdeal -> TransIdeal -> TransIdeal
join i j = idealTimes i j

-- | Compute the Kleene closure of a transition ideal
star :: TransIdeal -> TransIdeal
star f = go f where
  go i = let i' = join i (compose i f) in
    if Set.fromList i == Set.fromList i'
    then i
    else go i'

-- | Fast forwards the analysis based on a summary
--
--   Given a transition formula X' = P(X,Y) and
--   summary ideal I over F[X,X'], compose then map X' to temporaries
--   and canonicalize
fastForward :: (PseudoBoolean Var Angle, TransIdeal) -> State Ctx ()
fastForward (poly, summary) = do
  ctx <- get
  Trace.trace ("Ctx: \n" ++ show ctx ++ "\n") $ return ()
  Trace.trace ("poly: \n" ++ show poly ++ "\n") $ return ()
  Trace.trace ("summary: \n" ++ show summary ++ "\n") $ return ()
  let n = nVars ctx
  let t = nTemps ctx
  let (ids, st) = unzip . Map.toList $ ket ctx
  let trans = rbuchberger $ map (\(p,i) -> ofVar (Temp $ i+n+t)+p) $ zip st [0..]
  Trace.trace ("trans shifted: \n" ++ show trans ++ "\n") $ return ()
  let evars = [Temp $ i+n+t | i <- [0..n-1]]
  let poly' = (rename (shiftInits $ Just (t+n)) . rename (shiftPrimes $ Just t)) $ poly
  let sum'  = map (rename (shiftInits $ Just (t+n)) . rename (shiftPrimes $ Just t)) summary
  Trace.trace ("poly shifted: \n" ++ show poly' ++ "\n") $ return ()
  Trace.trace ("summary shifted: \n" ++ show sum' ++ "\n") $ return ()
  let ideal = idealPlus trans sum'
  Trace.trace ("transition ideal: \n" ++ show ideal  ++ "\n") $ return ()
  let pRed  = mvdInPP poly' ideal
  Trace.trace ("poly reduced: \n" ++ show pRed ++ "\n") $ return ()
  let trans' = eliminateVars evars $ ideal
  Trace.trace ("existentials removed: \n" ++ show trans' ++ "\n") $ return ()
  let ideal'= idealPlus ideal trans'
  let ket'  = Map.fromList $ zip ids (map (flip mvd trans') [ofVar (Temp $ i+t) | i <- [0..n-1]])
  let ctx'  = ctx { nTemps = t+n,
                    pp     = pp ctx + pRed,
                    ket    = ket',
                    ideal  = ideal'}
  Trace.trace ("Ctx': \n" ++ show ctx' ++ "\n") $ return ()
  put $ ctx'

-- | Summarizes a conditional
branchSummary :: Ctx -> Ctx -> State (Ctx) (PseudoBoolean Var Angle, TransIdeal)
branchSummary ctx' ctx'' = do
  let o1 = orphans ctx' ++ Map.elems (terms ctx')
  let o2 = orphans ctx'' ++ Map.elems (terms ctx'')
  modify (\ctx -> ctx { orphans = orphans ctx ++ o1 ++ o2 })
  let i1 = rbuchberger $ map (\(p,i) -> ofVar (Prime i) + p) $ zip (Map.elems $ ket ctx') [0..]
  let p1 = scale (Continuous (sqrt 2)) $ mvdInPP (pp ctx') i1
  let i2 = rbuchberger $ map (\(p,i) -> ofVar (Prime i) + p) $ zip (Map.elems $ ket ctx'') [0..]
  let p2 = scale (Continuous (sqrt 2)) $ mvdInPP (pp ctx'') i2
  return (p1+p2, join (eliminateAll i1) (eliminateAll i2))

-- | Summarizes a loop
--
--   First we eliminate any temporaries to get a transition ideal in F[X,X']
--   Next we take the fixpoint of T(I) = I * I' where I' = \exists X''. I[X'<-X''] + F[X'',X']
loopSummary :: Ctx -> State (Ctx) (PseudoBoolean Var Angle, TransIdeal)
loopSummary ctx' = do
  modify (\ctx -> ctx { orphans = orphans ctx ++ orphans ctx' ++ (Map.elems $ terms ctx') })
  -- First compute an elimination basis to canonicalize pp over [X,X']
  let ideal = rbuchberger $ map (\(p,i) -> ofVar (Prime i) + p) $ zip (Map.elems $ ket ctx') [0..]
  let pp'   = scale (Continuous (sqrt 2)) $ mvdInPP (pp ctx') ideal
  return (pp', star $ eliminateAll ideal) 

-- | Abstract transformers for while statements
applyStmt :: WStmt -> State (Ctx) ()
applyStmt stmt = case stmt of
  WSkip _      -> return ()
  WGate l gate -> applyGate (gate, l)
  WSeq _ s1 s2 -> applyStmt s1 >> applyStmt s2
  WReset _ v   -> getSt v >>= \bv -> setSt v 0
  WMeasure _ v -> getSt v >> return ()
  WIf _ s1 s2  -> do
    ctx <- get
    let vars  = Map.keys $ ket ctx
    let ctx'  = execState (processBlock s1) $ initialState vars vars
    let ctx'' = execState (processBlock s2) $ initialState vars vars
    summary <- branchSummary ctx' ctx''
    fastForward summary
  WWhile _ s   -> do
    ctx <- get
    let vars = Map.keys $ ket ctx
    let ctx' = execState (processBlock s) $ initialState vars vars
    summary <- loopSummary ctx'
    fastForward summary

-- | Analysis
processBlock :: WStmt -> State (Ctx) ()
processBlock stmt = applyStmt stmt >> computeIdeal >> reduceTerms

-- | Generate substitution list
genSubstList :: [ID] -> [ID] -> WStmt -> Map Loc Angle
genSubstList vars inputs stmt =

  let result = execState (processBlock stmt) $ initialState vars inputs
      phases = (Map.toList $ terms result) ++ [(1, t) | t <- orphans result]
      gphase = phase result

      go (poly, (locs, angle)) map =
        let (loc, angle') = case Set.findMin locs of
              (l, 0) -> (l, angle)
              (l, 1) -> (l, (-angle))
            update (l,_) = Map.insert l (if poly /= 0 && loc == l then angle' else 0)
        in
          Set.foldr update map locs

  in
    Trace.trace ("Final state: \n" ++ show result) $ foldr go Map.empty phases

-- | Apply substitution list
applyOpt :: Map Loc Angle -> WStmt -> WStmt
applyOpt opts stmt = go stmt where
  go stmt = case stmt of
    WSkip l      -> WSkip l
    WGate l gate -> case Map.lookup l opts of
      Nothing    -> WGate l gate
      Just angle ->
        let gatelist = synthesizePhase (getTarget gate) angle in
          foldr (WSeq l) (WSkip l) $ map (WGate l) gatelist
    WSeq l s1 s2 -> WSeq l (go s1) (go s2)
    WReset l v   -> stmt
    WMeasure l v -> stmt
    WIf l s1 s2  -> WIf l (go s1) (go s2)
    WWhile l s   -> WWhile l (go s)

  getTarget gate = case gate of
    T x    -> x
    S x    -> x
    Z x    -> x
    Tinv x -> x
    Sinv x -> x
    Rz _ x -> x

-- | Optimization algorithm
stateFoldpp :: [ID] -> [ID] -> WStmt -> WStmt
stateFoldpp vars inputs stmt = applyOpt opts stmt where
  opts = genSubstList vars inputs stmt

-- Testing
v = ["x", "y", "z"]

testcase1 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WWhile 4 $ WGate 5 $ CNOT "x" "y") $
            WGate 6 $ Tinv "x"

testcase2 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WIf 4 (WGate 5 $ CNOT "x" "y") (WSkip 6)) $
            WGate 7 $ Tinv "x"

testcase3 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WReset 4 "x") $
            WGate 5 $ T "x"

testcase4 = WSeq 1 (WGate 2 $ CNOT "x" "y") $
            WSeq 3 (WGate 4 $ T "y") $
            WSeq 5 (WGate 6 $ CNOT "x" "y") $
            WSeq 7 (WWhile 8 $ WGate 9 $ Swap "x" "y") $
            WSeq 10 (WGate 11 $ CNOT "x" "y") $
            WSeq 12 (WGate 13 $ Tinv "y") $
            WGate 14 $ CNOT "x" "y"

testcase5 = WSeq 1 (WGate 2 $ T "y") $
            WSeq 3 (WWhile 4 $ WGate 5 $ H "x") $
            WGate 6 $ Tinv "y"

testcase6 = WSeq 1 (WGate 2 $ T "y") $
            WSeq 3 (WWhile 4 $
                    WSeq 5 (WGate 6 $ T "x") $
                    WWhile 7 $ (WGate 8 $ X "y")) $
            WGate 9 $ Tinv "y"

testcase7 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WGate 4 $ H "x") $
            WSeq 5 (WWhile 6 $ WGate 7 $ T "y") $
            WSeq 8 (WGate 9 $ H "x") $
            WGate 10 $ Tinv "x"

testcase8 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WGate 4 $ H "x") $
            WSeq 5 (WWhile 6 $ WGate 7 $ T "x") $
            WSeq 8 (WGate 9 $ H "x") $
            WGate 10 $ Tinv "x"

testcase9 = WSeq 1 (WGate 2 $ T "y") $
            WSeq 3 (WWhile 4 $
                       WSeq 5 (WGate 6 $ Swap "x" "y") $
                       WGate 8 $ Swap "y" "z") $
            WGate 10 $ Tinv "y"

toStmt i xs = go i xs where
  go i []     = WSkip i
  go i (x:xs) = WSeq i (WGate (i+1) x) $ go (i+2) xs

testcase10 = WSeq 1 (WReset 2 "z") $
             WSeq 3 (toStmt 4 $ [X "x"] ++ ccx "x" "y" "z" ++ [T "z"] ++ ccx "x" "y" "z" ++ [X "x"]) $
             WSeq 100 (WWhile 101 $ WGate 102 $ CNOT "x" "y") $
             toStmt 103 $ [X "x"] ++ ccx "x" "y" "z" ++ [T "z"] ++ ccx "x" "y" "z" ++ [X "x"]