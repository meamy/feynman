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
import Control.Monad.State.Strict
import Data.Bits

import Feynman.Core
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

-- | The /i/th variable
var :: Int -> String
var i = "v" ++ show i

-- | The number of a variable
unvar :: String -> Int
unvar = read . tail

{-----------------------------------
 Optimization algorithm
 -----------------------------------}

data Ctx = Ctx {
  dim     :: Int,
  ket     :: Map ID (SBool String),
  terms   :: Map (SBool String) Term,
  phase   :: Angle,
  orphans :: [Term],
  pp      :: PseudoBoolean String Angle,
  paths   :: Set Int
} deriving Show

-- | Allocate a new variable
alloc :: State Ctx Int
alloc = do
  n <- gets dim
  modify $ \st -> st { dim = n + 1 }
  return n

-- | Get the state of variable v
getSt :: ID -> State Ctx (SBool String)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bexp -> return bexp
    Nothing -> do
      n <- alloc
      let bexp = ofVar $ var n
      setSt v bexp
      return bexp

-- | Set the state of a variable
setSt :: ID -> SBool String -> State Ctx ()
setSt v bexp = modify $ \st -> st { ket = Map.insert v bexp (ket st) }

-- | Adds a mergeable phase term
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

-- | Adds a quadratic phase term
addQuadTerm :: SBool String -> SBool String -> State Ctx ()
addQuadTerm bexp bexp' = modify $ \st -> st { pp = pp st + poly } where
  poly = P.lift $ bexp * bexp'

-- | Remove an internal variable
elimVar :: Int -> State Ctx ()
elimVar x = modify $ \st -> st { pp = remVar (var x) $ pp st }

-- | Substitute a variable
substVar :: Int -> SBool String -> State Ctx ()
substVar x bexp = modify go where
  go st = st { terms = Map.mapKeysWith c f $ terms st,
               pp    = P.subst (var x) bexp $ pp st,
               ket   = Map.map (P.subst (var x) bexp) $ ket st }
  f = dropConstant . P.subst (var x) bexp
  c (s1, a1) (s2, a2) = (Set.union s1 s2, a1 + a2)

-- | Matches a instance of [HH] with maximum degree /cutoff/
matchHH :: PseudoBoolean String Angle -> Set Int -> Set Int -> Maybe Int -> Maybe (Int, Int, SBool String)
matchHH pp cand paths cutoff = msum . map (go . var) $ Set.toDescList cand where
  go v = do
    pp'      <- toBooleanPoly . quotVar v $ pp
    (u, sub) <- find validSoln $ solveForX pp'
    return (unvar v, unvar u, sub)
  validSoln (u, sub) = case cutoff of
    Just d  -> degree sub <= d && Set.member (unvar u) paths
    Nothing -> Set.member (unvar u) paths

-- | Finding [HH] reductions
applyReductions :: Maybe Int -> State Ctx [SBool String]
applyReductions cutoff = do
  poly     <- gets pp
  pathVars <- gets paths
  outVars  <- gets (Set.unions . map (Set.map unvar . vars) . Map.elems . ket)
  case matchHH poly (Set.difference pathVars outVars) pathVars cutoff of
    Nothing           -> return []
    Just (x, y, bexp) -> do
      elimVar x
      substVar y bexp
      xs <- applyReductions cutoff
      return $ (ofVar (var y) + bexp):xs

-- | Reduce with respect to a groebner basis for a set of polynomials
reduceAll :: [SBool String] -> State Ctx ()
reduceAll ideal = do
  st <- get
  let gbasis = reduceBasis $ buchberger ideal
  let comb (s,a) (t,b) = (Set.union s t, a + b)
  put $ st { terms = Map.mapKeysWith comb (flip mvd gbasis) $ terms st }

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

-- | The initial state
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty 0 [] 0 Set.empty where
  dim = 1 + length inputs
  ket = (zip inputs [ofVar (var x) | x <- [0..]]) ++ (zip (vars\\inputs) $ repeat 0)
  
-- | Apply the transformers for a list of gates and reduce the result
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState $ do
  mapM_ applyGate (zip circ [2..])
  i1 <- applyReductions (Just 1) -- linear reductions
  i2 <- applyReductions (Just 2) -- quadratic reductions
  ik <- applyReductions Nothing -- all other reductions
  --reduceAll $ i1 ++ i2 ++ ik
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

-- | Fast forwards the analysis based on a summary
{-
fastForward :: AffineRelation -> State Ctx ()
fastForward summary = do
  ctx <- get
  Trace.trace ("Ctx: \n" ++ show ctx) $ return ()
  Trace.trace ("summary: \n" ++ show summary) $ return ()
  let (ids, vecs) = unzip . Map.toList $ ket ctx
  let vecs' = vals $ compose' (makeExplicit . ARD . fromList $ vecs) summary
  let ket' = Map.fromList $ zip ids vecs'
  let dim' = width $ head vecs'
  let tms'  = Map.mapKeysMonotonic (extendLeft (dim' - dim ctx)) $ terms ctx
  let ctx'  = ctx { dim   = dim',
                    ket   = ket',
                    terms = tms' }
  Trace.trace ("Ctx': \n" ++ show ctx') $ return ()
  put $ ctx'
-}

-- | Summarizes a conditional
{-
branchSummary :: Ctx -> Ctx -> State (Ctx) AffineRelation
branchSummary ctx' ctx'' = do
  let o1  = orphans ctx' ++ Map.elems (terms ctx')
  let ar1 = makeExplicit . ARD . fromList . Map.elems $ ket ctx'
  let o2 = orphans ctx'' ++ Map.elems (terms ctx'')
  let ar2 = makeExplicit . ARD . fromList . Map.elems $ ket ctx''
  modify (\ctx -> ctx { orphans = orphans ctx ++ o1 ++ o2 } )
  return $ join ar1 ar2
-}

-- | Summarizes a loop
{-
loopSummary :: Ctx -> State (Ctx) AffineRelation
loopSummary ctx' = do
  modify (\ctx -> ctx { orphans = orphans ctx ++ orphans ctx' ++ (Map.elems $ terms ctx') })
  return $ star . projectTemporaries . makeExplicit . ARD . fromList . Map.elems $ ket ctx'
-}

-- | Abstract transformers for while statements
applyStmt :: WStmt -> State (Ctx) ()
applyStmt stmt = case stmt of
  WSkip _      -> return ()
  WGate l gate -> applyGate (gate, l)
  WSeq _ s1 s2 -> applyStmt s1 >> applyStmt s2
  WReset _ v   -> getSt v >>= \bv -> setSt v 0
  WMeasure _ v -> getSt v >> return ()
  {-
  WIf _ s1 s2  -> do
    ctx <- get
    let vars  = Map.keys $ ket ctx
    let ctx'  = execState (applyStmt s1) $ initialState vars vars
    let ctx'' = execState (applyStmt s2) $ initialState vars vars
    summary <- branchSummary ctx' ctx''
    fastForward summary
  WWhile _ s   -> do
    ctx <- get
    let vars = Map.keys $ ket ctx
    let ctx' = execState (applyStmt s) $ initialState vars vars
    summary <- loopSummary ctx'
    fastForward summary
-}

-- | Generate substitution list
genSubstList :: [ID] -> [ID] -> WStmt -> Map Loc Angle
genSubstList vars inputs stmt =

  let result = execState (applyStmt stmt) $ initialState vars inputs
      phases = (snd . unzip . Map.toList $ terms result) ++ orphans result
      gphase = phase result

      go (locs, angle) map =
        let (loc, angle') = case Set.findMin locs of
              (l, 0) -> (l, angle)
              (l, 1) -> (l, (-angle))
            update (l,_) = Map.insert l (if loc == l then angle' else 0)
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
