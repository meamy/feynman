{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : PhaseFold
Description : Phase folding optimization
Copyright   : (c) Matthew Amy, 2022
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

The phase folding optimization pass. Different representations of
affine parity functions can be swapped in a la ML functors
-}

module Feynman.Optimization.PhaseFold(
  phaseFold,
  phaseFoldFast,
  phaseFoldAlt
  ) where

import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Functor.Identity
import Data.Coerce
import Data.Bits

import Control.Monad.State.Strict

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase
import Feynman.Optimization.ARD

import qualified Debug.Trace as Trace

{-----------------------------------
 Utilities
 -----------------------------------}

-- | Terms of the phase polynomial
type Term = (Set (Loc, Bool), Angle)

-- | The type of an analysis with an underlying parity representation
newtype Analysis repr = Analysis ([ID] -> [ID] -> [Primitive] -> ([Term], Angle))

-- | Type class for the representation of affine parities in /n/ variables.
--   Roughly, isomorphic to \(2^{[n]}\times \mathbb{Z}_2\)
class (Eq parity, Ord parity) => Parity parity where
  (.+.) :: parity -> parity -> parity
  split :: parity -> (parity, Bool)
  comb  :: (parity, Bool) -> parity
  nil   :: parity
  var   :: Int -> parity
  proj1 :: parity -> parity
  proj2 :: parity -> Bool
  inj1  :: parity -> parity
  inj2  :: Bool -> parity
  isNil :: parity -> Bool
  -- Other operators
  proj1 = fst . split
  proj2 = snd . split
  inj1  = \a -> comb (a,False)
  inj2  = \a -> comb (nil,a)
  isNil = (nil ==)
  
-- | Defines an instance where the lowest-order bit is the affine value
instance Parity F2Vec where
  a .+. b    = a + b
  split a    = (zeroExtend (-1) $ shiftR a 1, testBit a 0)
  comb (a,b) = if b then setBit a' 0 else a' where a' = (flip shiftL) 1 $ zeroExtend 1 a
  nil        = 0
  var i      = bitI (max 32 (i+1)) i

-- | Defines an instance where 0 is the affine value
instance Parity IntSet where
  a .+. b    = symDiff a b
  split a    = (IntSet.delete 0 a, IntSet.member 0 a)
  comb (a,b) = if b then IntSet.insert 0 a else a
  nil        = IntSet.empty
  var i      = IntSet.singleton i

-- | Symmetric difference implementation for int sets
symDiff :: IntSet -> IntSet -> IntSet
symDiff = IntSet.foldr (\k s -> c $ IntSet.alterF (fmap not . pure) k s) where
  c = coerce :: Identity IntSet -> IntSet

{-----------------------------------
 Optimization algorithm
 -----------------------------------}

-- | Context maintained during the analysis phase
data Ctx parity = Ctx {
  dim     :: Int,
  ket     :: Map ID parity,
  terms   :: Map parity Term,
  orphans :: [Term],
  phase   :: Angle
} deriving Show

-- | Get the (affine) parity for variable v, or otherwise allocate one
getSt :: Parity parity => ID -> State (Ctx parity) (parity)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket' }
                  return (bv')
      where dim' = dim st + 1
            bv'  = var dim'
            ket' = Map.insert v bv' (ket st)

-- | Set the state of a variable as an (affine) parity
setSt :: Parity parity => ID -> parity -> State (Ctx parity) ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv $ ket st }

-- | Increases the dimension (i.e. number of variables tracked)
increaseDim :: State (Ctx parity) (Int)
increaseDim = get >>= \st -> do
  let dim' = dim st + 1
  put $ st { dim = dim' }
  return dim'

-- | Applies a rotation of a given angle on a particular (affine) parity
addTerm :: Parity parity => Angle -> Loc -> parity -> State (Ctx parity) ()
addTerm theta loc aparity = modify go where
  theta' = if isNil aparity then 0 else theta
  go st = case split aparity of
    (parity, False) -> st { terms = Map.alter (add theta') parity $ terms st }
    (parity, True)  -> st { terms = Map.alter (add (-theta')) parity $ terms st,
                            phase = phase st + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, proj2 aparity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, proj2 aparity), theta)

-- | Abstract transformers for primitive gates
applyGate :: Parity parity => (Primitive, Loc) -> State (Ctx parity) ()
applyGate (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \bv -> setSt v (bv .+. inj2 True)
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (bv .+. bv')
  CZ c t -> return ()  -- N-op wrt phase folding
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    mapM_ (\v -> increaseDim >>= \k -> setSt v $ var k) args

-- | Initial state given a set of variables and specified inputs
initialState :: Parity parity => [ID] -> [ID] -> Ctx parity
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = (zip inputs [(var x) | x <- [1..]]) ++ (zip (vars \\ inputs) [nil | x <- [1..]])

-- | Run the analysis on a circuit and state
runCircuit :: Parity parity => [Primitive] -> Ctx parity -> Ctx parity
runCircuit circ = execState (mapM_ applyGate $ zip circ [2..])

-- | Encapsulates a parity representation into a generic circuit analyzer
mkAnalyzer :: forall repr . Parity repr => Analysis repr
mkAnalyzer = Analysis (analysis)
  where analysis vars inputs circ =
          let result :: Ctx repr
              result = runCircuit circ $ initialState vars inputs
          in
            ((snd . unzip . Map.toList $ terms result), phase result)

-- | Run the analysis with a given analyzer and merge the phase gates
phaseFoldGen :: Analysis repr -> [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFoldGen (Analysis f) vars inputs circ =
  let (phases, gphase0) = f vars inputs circ
      (map, gphase) = foldr go (Map.empty, gphase0) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, False) -> (l, gphase, angle)
                (l, True)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if loc == l then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
      circ' = concatMap go (zip circ [2..]) where
        go (gate, l) = case Map.lookup l map of
          Nothing -> [(gate, l)]
          Just angle
            | angle == 0 -> []
            | otherwise  -> zip (synthesizePhase (getTarget gate) angle) [0..]
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
 Existential version
 -----------------------------------}

-- | The analysis context restricted for existential quantification
type ExtCtx = Ctx F2Vec

-- | Existentially quantifies a variable.
--
--   Any term that no longer has a representative becomes orphaned after
--   existential quantification and can no longer participate in any merging.
--   In theory this could both reduce memory cost and speed things up
--   if the number of active terms grows too large without quantification.
--   In practice it seems usually this ends up being slower
exists :: ID -> ExtCtx -> ExtCtx
exists v st@(Ctx dim ket terms orphans phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v ket
      normLen vec   = zeroExtend (dim - width vec) vec
      (vecs, cnsts) = unzip $ map ((\(a,b) -> (normLen a, b)) . split) avecs
      (t, o)        = Map.partitionWithKey (\b _ -> inLinearSpan vecs $ normLen b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = map comb $ zip vecs' (cnsts ++ [False])
      orphans'      = (snd $ unzip $ Map.toList o) ++ orphans
      terms'        = if dim' > dim
                      then Map.mapKeysMonotonic (zeroExtend 1) t
                      else t
  in
    Ctx dim' (Map.fromList $ zip (vars ++ [v]) avecs') terms' orphans' phase

-- | The analysis using existential quantification
applyGateExist :: (Primitive, Loc) -> State ExtCtx ()
applyGateExist (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \bv -> setSt v (bv .+. inj2 True)
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (bv .+. bv')
  CZ c t -> return ()  -- N-op wrt phase folding
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    mapM_ (\v -> modify $ exists v) args

-- | Run the analysis using existential quantification
runCircuitAlt :: [Primitive] -> ExtCtx -> ExtCtx
runCircuitAlt circ = execState (mapM_ applyGateExist $ zip circ [2..])

-- | Analyzer using existentials, for use in the generic algorithm
phaseAnalysisAlt :: Analysis ExtCtx
phaseAnalysisAlt = Analysis go where
  go vars inputs circ =
    let result = runCircuitAlt circ $ initialState vars inputs in
      ((snd . unzip . Map.toList $ terms result) ++ (orphans result), phase result)

{-----------------------------------
 Specific instances
 -----------------------------------}

-- | Via int sets. Fast and sparse
phaseFold = phaseFoldGen (mkAnalyzer :: Analysis IntSet)

-- | Via bitvectors. Faster but high memory
phaseFoldFast = phaseFoldGen (mkAnalyzer :: Analysis F2Vec)

-- | Via minimal-width bitvectors. Slow but best memory usage
phaseFoldAlt = phaseFoldGen phaseAnalysisAlt


{-----------------------------------
 Phase folding of the quantum WHILE
 -----------------------------------}

-- | Temporary, as we need vectors to have the same length here
initialState' :: [ID] -> [ID] -> Ctx F2Vec
initialState' vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = (zip inputs [bitI (dim+1) x | x <- [1..]]) ++
        (zip (vars \\ inputs) [bitVec (dim+1) 0 | x <- [1..]])

-- | Fast forwards the analysis based on a (fast-forward) summary
fastForward :: AffineRelation -> State (Ctx F2Vec) ()
fastForward summary = do
  ctx <- get
  Trace.trace ("Ctx: \n" ++ show ctx) $ return ()
  Trace.trace ("summary: \n" ++ show summary) $ return ()
  let ar     = makeExplicit . ARD . fromList . map (flip rotate (-1)) . Map.elems $ ket ctx
  Trace.trace ("Ar: \n" ++ show ar) $ return ()
  let cns    = cOp ar summary
  Trace.trace ("Cop: \n" ++ show cns) $ return ()
  let ket'   = Map.fromList $ zip (Map.keys $ ket ctx) [bitI ((dim ctx)+1) x | x <- [1..]]
  Trace.trace ("Ket': \n" ++ show ket') $ return ()
  let (o,t)  = foldl' go (orphans ctx, []) (Map.toList $ terms ctx) where
        go (o,t) (bv, tm) = Trace.trace (show "Canonical form of " ++ show bv ++ ":\n" ++ show
                                         (projectVector cns (append (bitVec 1 0) bv))) $ case projectVector cns (append (bitVec 1 0) bv) of
          Nothing  -> (tm:o, t)
          Just bv' -> (o, (proj1 $ rotate bv' 1,tm):t)
  let ctx' = ctx { ket     = ket',
                   terms   = Map.fromList t,
                   orphans = o }
  Trace.trace ("Ctx': \n" ++ show ctx') $ return ()
  put $ ctx { ket     = ket',
              terms   = Map.fromList t,
              orphans = o }

-- | Summarizes a conditional
branchSummary :: Ctx F2Vec -> Ctx F2Vec -> State (Ctx F2Vec) AffineRelation
branchSummary ctx' ctx'' = do
  let o1  = orphans ctx' ++ Map.elems (terms ctx')
  let ar1 = makeExplicitFF . ARD . fromList . map (flip rotate (-1)) . Map.elems $ ket ctx'
  let o2 = orphans ctx'' ++ Map.elems (terms ctx'')
  let ar2 = makeExplicitFF . ARD . fromList . map (flip rotate (-1)) . Map.elems $ ket ctx''
  modify (\ctx -> ctx { orphans = orphans ctx ++ o1 ++ o2 } )
  return $ joinFF ar1 ar2

-- | Summarizes a loop
loopSummary :: Ctx F2Vec -> State (Ctx F2Vec) AffineRelation
loopSummary ctx' = do
  modify (\ctx -> ctx { orphans = orphans ctx ++ orphans ctx' ++ (Map.elems $ terms ctx') })
  return $ starFF . makeExplicitFF . ARD . fromList . map (flip rotate (-1)) . Map.elems $ ket ctx'

{-
-- | Post-composes a with b|c
applyBranch :: Ctx F2Vec -> Ctx F2Vec -> Ctx F2Vec -> Ctx F2Vec
applyBranch ctx ctx' ctx'' =
  let ar1 = makeExplicit . ARD . fromList . Map.elems $ ket ctx
      ar2 = makeExplicitFF . ARD . fromList . Map.elems $ ket ctx'
      ar3 = makeExplicitFF . ARD . fromList . Map.elems $ ket ctx''
      cns = cOp ar1 $ joinFF ar2 ar3

  constraintSolver = cOp $ joinFF genJoin (ket ctx') (ket ctx'')

-- | Post-composes a with b*
applyLoop :: Ctx F2Vec -> Ctx F2Vec -> Ctx F2Vec
applyLoop ctx ctx' = Ctx dim ket' terms' orphans' phase where
  constraints = genStar (ket ctx')
  (terms, orphaned)
  phases' = orphans ctx' ++ (snd . unzip . Map.toList $ terms ctx')
-}
  
-- | Abstract transformers for while statements
applyStmt :: WStmt -> State (Ctx F2Vec) ()
applyStmt stmt = case stmt of
  WSkip _      -> return ()
  WGate l gate -> applyGate (gate, l)
  WSeq _ s1 s2 -> applyStmt s1 >> applyStmt s2
  WReset _ v   -> getSt v >>= \bv -> setSt v (bitVec (width bv) 0)
  WMeasure _ v -> getSt v >> return ()
  WIf _ s1 s2  -> do
    ctx <- get
    let vars  = Map.keys $ ket ctx
    let ctx'  = execState (applyStmt s1) $ initialState' vars vars
    let ctx'' = execState (applyStmt s2) $ initialState' vars vars
    summary <- branchSummary ctx' ctx''
    fastForward summary
  WWhile _ s   -> do
    ctx <- get
    let vars = Map.keys $ ket ctx
    let ctx' = execState (applyStmt s) $ initialState' vars vars
    --Trace.trace (show ctx) $ return ()
    --Trace.trace (show ctx') $ return ()
    summary <- loopSummary ctx'
    --Trace.trace (show summary) $ return ()
    fastForward summary

-- | Generate substitution list
genSubstList :: [ID] -> [ID] -> WStmt -> Map Loc Angle
genSubstList vars inputs stmt =

  let result = execState (applyStmt stmt) $ initialState' vars inputs
      phases = (snd . unzip . Map.toList $ terms result) ++ orphans result
      gphase = phase result

      go (locs, angle) map =
        let (loc, angle') = case Set.findMin locs of
              (l, False) -> (l, angle)
              (l, True)  -> (l, (-angle))
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
phaseFoldpp :: [ID] -> [ID] -> WStmt -> WStmt
phaseFoldpp vars inputs stmt = applyOpt opts stmt where
  opts = genSubstList vars inputs stmt

-- Testing
vars = ["x", "y"]
testcase1 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WWhile 4 $ WGate 5 $ CNOT "x" "y") $
            WGate 6 $ Tinv "x"
test1 = genSubstList vars vars testcase1
test2 = execState (applyStmt testcase1) (initialState' vars vars)

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
