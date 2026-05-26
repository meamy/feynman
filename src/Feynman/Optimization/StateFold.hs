{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : State fold
Description : state folding optimization
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

-}

module Feynman.Optimization.StateFold(
  stateFold,
  pauliFold,
  stateAnalysispp,
  stateFoldpp,
  summarizeLoops
  ) where

import Data.List hiding (transpose)
import Data.Maybe
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (msum, liftM)
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

import Feynman.Optimization.Clifford


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

-- | Adds a non-mergeable phase term
addTerm' :: Angle -> SBool Var -> State Ctx ()
addTerm' theta bexp = modify $ \st -> st { pp = pp st + poly } where
  poly = distribute theta bexp

-- | Remove a variable
elimVar :: Var -> State Ctx ()
elimVar x = modify $ \st -> st { pp = remVar x $ pp st }

-- | Substitute a variable
substVar :: Var -> SBool Var -> State Ctx ()
substVar x bexp = modify go where
  go st = st { terms = applyToPP $ terms st,
               pp    = P.subst x bexp $ pp st,
               ket   = Map.map (P.subst x bexp) $ ket st }

  applyToPP terms =
    let (y, n) = Map.partitionWithKey (\m _ -> Set.member x $ vars m) terms
        y'     =
          if getConstant bexp == 1
          then Map.map (\(s, a) -> (Set.map (\(l,p) -> (l,1+p)) s, -a)) y
          else y
        y''    = Map.mapKeysWith c f $ y'
    in
      Map.unionWith c y'' n

  f = dropConstant . P.subst x bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

-- | Matches a instance of [I] with maximum degree /cutoff/
matchI :: PseudoBoolean Var Angle -> Set Var -> Maybe Int -> [SBool Var]
matchI pp cand cutoff = filter isValid . catMaybes . map go $ Set.toAscList cand where
  go v = toBooleanPoly . quotVar v $ pp
  isValid pp = case cutoff of
    Just d  -> degree pp <= d
    Nothing -> True

-- | Matches an instance of [HH] with maximum degree /cutoff/
matchHH :: PseudoBoolean Var Angle -> Set Var -> Maybe Int -> Maybe (Var, Var, SBool Var)
matchHH pp cand cutoff = msum . map go $ Set.toAscList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (v, u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && isTemp u
    Nothing -> isTemp u

-- | Matches an instance of the [omega] rule
matchOmega :: PseudoBoolean Var Angle -> Set Var -> Maybe (Var, SBool Var)
matchOmega pp cand = msum . map go $ Set.toAscList cand where
  go v = do
    pp' <- toBooleanPoly . addFactor v $ pp
    return (v, pp')
  addFactor v p = constant (Discrete $ fromDyadic $ dyadic 3 1) + quotVar v p

-- | Finding [HH] reductions
applyReductions :: Maybe Int -> State Ctx [SBool Var]
applyReductions cutoff = do
  poly     <- gets pp
  let temps = Set.filter (isTemp) $ vars poly
  exposed  <- gets (Set.filter (isTemp) . Set.unions . map vars . Map.elems . ket)
  let ideal = matchI poly (Set.difference temps exposed) cutoff
  let hhIst = matchHH poly (Set.difference temps exposed) cutoff
  let omIst = matchOmega poly (Set.difference temps exposed)
  case (hhIst, omIst) of
    (Just (x, y, bexp), _)    -> do
      elimVar x
      substVar y bexp
      xs <- applyReductions cutoff
      return $ (ofVar y + bexp):xs
    (Nothing, Just (x, bexp)) -> do
      elimVar x
      let poly = constFactor + polyFactor where
            constFactor = constant (Discrete $ fromDyadic $ dyadic 1 2)
            polyFactor  = distribute (Discrete $ fromDyadic $ dyadic 3 1) (P.lift bexp)
      modify (\st -> st { pp = pp st + poly })
      xs <- applyReductions cutoff
      return $ xs
    (Nothing, Nothing)        -> return []

-- | Reduce with respect to a groebner basis for a set of polynomials
reduceTerms :: State Ctx ()
reduceTerms = do
  st <- get
  let comb (s,a) (t,b) = (Set.union s t, a + b)
  put $ st { terms = Map.mapKeysWith comb (flip mvd $ ideal st) $ terms st }

-- | Computes an ideal for the state
computeIdeal :: Int -> State Ctx ()
computeIdeal cutoff = do
  i1 <- applyReductions (Just 1)      -- linear reductions
  id <- case cutoff of
    1         -> return []
    x | x > 1 -> applyReductions (Just cutoff) -- reductions up to the degree cutoff
    x | x < 1 -> applyReductions Nothing -- all other reductions
  return ()
  --reduceAll $ rbuchberger $ i1 ++ id
  --return $ i1 ++ id

-- | Abstract transformers for individual gates
applyGate :: Bool -> (Primitive, Loc) -> State Ctx ()
applyGate tonly (gate, l) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) l
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) l
  S v    -> getSt v >>= if tonly
    then addTerm' (dyadicPhase $ dyadic 1 1)
    else addTerm (dyadicPhase $ dyadic 1 1) l
  Sinv v -> getSt v >>= if tonly
    then addTerm' (dyadicPhase $ dyadic 3 1)
    else addTerm (dyadicPhase $ dyadic 3 1) l
  Z v    -> getSt v >>= if tonly
    then addTerm' (dyadicPhase $ dyadic 1 0)
    else addTerm (dyadicPhase $ dyadic 1 0) l
  Rz p v -> getSt v >>= addTerm p l
  CNOT c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    setSt t (bexp + bexp')
  CZ c t -> do
    bexp  <- getSt c
    bexp' <- getSt t
    addTerm' (Discrete $ fromDyadic $ dyadic 1 0) (bexp * bexp')
  X v -> do
    bexp <- getSt v
    setSt v (1 + bexp)
  H v -> do
    bexp <- getSt v
    v'   <- liftM ofVar $ allocTemp
    addTerm' (Discrete $ fromDyadic $ dyadic 1 0) (bexp * v')
    setSt v v' 
  Swap u v -> do
    bexp  <- getSt u
    bexp' <- getSt v
    setSt u bexp'
    setSt v bexp
  _        -> do
    let args = getArgs gate
    mapM_ getSt args
    xs <- mapM (\_ -> allocTemp) [0..length args - 1]
    mapM_ (\i -> addTerm' (Continuous (sqrt 2)) (ofVar i)) $ xs
    mapM_ (\(v,i) -> setSt v (ofVar i)) $ zip args xs

-- | The initial state
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx nVars 0 (Map.fromList ket) Map.empty 0 [] 0 [] where
  nVars = length inputs
  ket = (zip inputs [ofVar (Init x) | x <- [0..]]) ++ (zip (vars\\inputs) $ repeat 0)
  
-- | Apply the transformers for a list of gates and reduce the result
runCircuit :: Bool -> Int -> [AnnotatedPrimitive] -> Ctx -> Ctx
runCircuit tonly cutoff circ = execState $ do
  mapM_ (applyGate tonly) circ
  i1 <- applyReductions (Just 1) -- linear reductions
  id <- case cutoff of
    1         -> return []
    x | x > 1 -> applyReductions (Just cutoff) -- reductions up to the degree cutoff
    x | x < 1 -> applyReductions Nothing -- all other reductions
  --reduceAll $ rbuchberger $ i1 ++ i2 ++ ik
  return ()

-- | The stateFold optimization on circuits
stateFold :: Int -> [ID] -> [ID] -> [Primitive] -> [Primitive]
stateFold d vars inputs circ = unannotate $ applyOpt result circ' where
  circ'  = annotate circ
  result = stateAnalysis False d vars inputs circ'

-- | The stateFold optimization with CNOTs virtually expanded
pauliFold :: Int -> [ID] -> [ID] -> [Primitive] -> [Primitive]
pauliFold d vars inputs circ = unannotate $ applyOpt result circ' where
  circ'  = annotate circ
  f      = simplifyCliffords' . simplifyPrimitive' . expandCNOT'
  result = stateAnalysis True d vars inputs . f $ circ'

-- | The master statefolding method
stateAnalysis :: Bool -> Int -> [ID] -> [ID] -> [AnnotatedPrimitive] -> Map Loc Angle
stateAnalysis tonly d vars inputs circ =
  let result = runCircuit tonly d circ $ initialState vars inputs
      phases = Map.elems $ terms result
      (map, gphase) = foldr go (Map.empty, phase result) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, 0) -> (l, gphase, angle)
                (l, 1)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if l == loc then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
  in
    map

-- | Applies the statefolding optimization
applyOpt :: Map Loc Angle -> [AnnotatedPrimitive] -> [AnnotatedPrimitive]
applyOpt map circ =
  let circ' = concatMap go circ where
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
    circ' -- ++ (annotateWith (-1) $ globalPhase (head vars) gphase)

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
  let n = nVars ctx
  let t = nTemps ctx
  let (ids, st) = unzip . Map.toList $ ket ctx
  let trans = rbuchberger $ map (\(p,i) -> ofVar (Temp $ i+n+t)+p) $ zip st [0..]
  let evars = [Temp $ i+n+t | i <- [0..n-1]]
  let poly' = (rename (shiftInits $ Just (t+n)) . rename (shiftPrimes $ Just t)) $ poly
  let sum'  = map (rename (shiftInits $ Just (t+n)) . rename (shiftPrimes $ Just t)) summary
  let ideal = idealPlus trans sum'
  let pRed  = mvdInPP poly' ideal
  let trans' = eliminateVars evars $ ideal
  let ideal'= idealPlus ideal trans'
  let ket'  = Map.fromList $ zip ids (map (flip mvd trans') [ofVar (Temp $ i+t) | i <- [0..n-1]])
  let ctx'  = ctx { nTemps = t+n,
                    pp     = pp ctx + pRed,
                    ket    = ket',
                    ideal  = ideal'}
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
  let summ = join (eliminateAll i1) (eliminateAll i2)
  return (p1+p2, summ)

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
  let summ  = star $ eliminateAll ideal
  return (pp', summ) 

-- | Abstract transformers for while statements
applyStmt :: Int -> WStmt Loc -> State (Ctx) [String]
applyStmt d stmt = case stmt of
  WSkip _      -> return []
  WGate l gate -> applyGate False (gate, l) >> return []
  WSeq _ xs    -> liftM concat $ mapM (applyStmt d) xs
  WReset _ v   -> getSt v >>= \bv -> setSt v 0 >> return []
  WMeasure _ v -> getSt v >> return []
  WIf _ s1 s2  -> do
    ctx <- get
    let vars  = Map.keys $ ket ctx
    let (a,ctx')  = runState (processBlock d s1) $ initialState vars vars
    let (b,ctx'') = runState (processBlock d s2) $ initialState vars vars
    summary <- branchSummary ctx' ctx''
    fastForward summary
    return $ a ++ b
  WWhile l s   -> do
    ctx <- get
    let vars = Map.keys $ ket ctx
    let (a,ctx') = runState (processBlock d s) $ initialState vars vars
    summary <- loopSummary ctx'
    fastForward summary
    return $ a ++ ["Summary of loop at pos " ++ show l ++ ": " ++ show (snd summary)]

-- | Analysis
processBlock :: Int -> WStmt Loc -> State (Ctx) [String]
processBlock d stmt = do
  summaries <- applyStmt d stmt
  computeIdeal d
  reduceTerms
  return summaries

-- | Generate substitution list
stateAnalysispp :: Int -> [ID] -> [ID] -> WStmt Loc -> Map Loc Angle
stateAnalysispp d vars inputs stmt =

  let result = execState (processBlock d stmt) $ initialState vars inputs
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
    foldr go Map.empty phases

-- | Apply substitution list
applyOptpp :: Map Loc Angle -> WStmt Loc -> WStmt Loc
applyOptpp opts stmt = go stmt where
  go stmt = case stmt of
    WSkip l      -> WSkip l
    WGate l gate -> case Map.lookup l opts of
      Nothing    -> WGate l gate
      Just angle ->
        let gatelist = synthesizePhase (getTarget gate) angle in
          WSeq l $ map (WGate l) gatelist
    WSeq l xs    -> WSeq l (map go xs)
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
stateFoldpp :: Int -> [ID] -> [ID] -> WStmt Loc -> WStmt Loc
stateFoldpp d vars inputs stmt = applyOptpp opts stmt where
  opts = stateAnalysispp d vars inputs stmt

-- | Returns just the loop summaries
summarizeLoops :: Int -> [ID] -> [ID] -> WStmt Loc -> [String]
summarizeLoops d vars inputs stmt = xs where
  xs = evalState (processBlock d stmt) $ initialState vars inputs

