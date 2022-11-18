module Feynman.Optimization.PhaseFold where

import Data.List hiding (transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Control.Monad.State.Strict
import Data.Functor.Identity
import Data.Coerce
import Data.Bits

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Synthesis.Phase

{-- Phase folding optimization -}

type Term = (Set (Loc, Bool), Angle)
type Analyzer = [ID] -> [ID] -> [Primitive] -> ([Term], Angle)

{- Class of representations of affine parities -}
class Ord parity => Parity parity where
  (.+.) :: parity -> parity -> parity
  proj1 :: parity -> parity
  proj2 :: parity -> Bool
  inj   :: Int -> parity
  isNil :: parity -> Bool

instance Parity F2Vec where
  a .+. b = a + b
  proj1 a = clearBit a 0
  proj2 a = testBit a 0
  inj i   = bitI (i+1) i
  isNil a = a == 0

instance Parity IntSet where
  a .+. b = symDiff a b
  proj1 a = IntSet.delete 0 a
  proj2 a = IntSet.member 0 a
  inj i   = IntSet.singleton i
  isNil a = a == IntSet.empty

{- Symmetric difference for int sets -}
symDiff :: IntSet -> IntSet -> IntSet
symDiff = IntSet.foldr (\k s -> (coerce :: Identity IntSet -> IntSet) $ IntSet.alterF (fmap not . pure) k s)

{- Run the analysis and merge phase gates -}
phaseFoldGen :: Analyzer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFoldGen f vars inputs circ =
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

data Ctx parity = Ctx {
  dim     :: Int,
  ket     :: Map ID parity,
  terms   :: Map parity Term,
  orphans :: [Term],
  phase   :: Angle
} deriving Show


{-- Existential quantifiction based -}

type ExtCtx = Ctx F2Vec

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: Parity parity => ID -> State (Ctx parity) (parity)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket' }
                  return (bv')
      where dim' = dim st + 1
            bv'  = inj dim'
            ket' = Map.insert v bv' (ket st)

{- Set the state of a variable -}
setSt :: Parity parity => ID -> parity -> State (Ctx parity) ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv $ ket st }

{- Set the state of a variable -}
increaseDim :: State (Ctx parity) (Int)
increaseDim = get >>= \st -> do
  let dim' = dim st + 1
  put $ st { dim = dim' }
  return dim'
  
{- Existentially quantifies a variable. In particular, any term that no
 - longer has a representative becomes an "orphan" -- a term with
 - no current representative -}
exists :: ID -> ExtCtx -> ExtCtx
exists v st@(Ctx dim ket terms orphans phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v ket
      norm vec      = zeroExtend (dim + 1 - width vec) $ shiftR vec 1
      (vecs, cnsts) = (map norm avecs, map proj2 avecs)
      (t, o)        = Map.partitionWithKey (\b _ -> inLinearSpan vecs $ norm b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = map (\(vec, cnst) -> if cnst then vec .+. inj 0 else vec) $ zip vecs' $ cnsts ++ [False]
      orphans'      = (snd $ unzip $ Map.toList o) ++ orphans
      terms'        = if dim' > dim
                      then Map.mapKeysMonotonic (zeroExtend 1) t
                      else t
  in
    Ctx dim' (Map.fromList $ zip (vars ++ [v]) avecs') terms' orphans' phase

{- Adds a mergeable phase term -}
addTerm :: Parity parity => Angle -> Loc -> parity -> State (Ctx parity) ()
addTerm theta loc bv = modify go where
  theta' = if isNil bv then 0 else theta
  go st = case proj2 bv of
    False -> st { terms = Map.alter (add theta') bv $ terms st }
    True  -> st { terms = Map.alter (add (-theta')) (bv .+. inj 0) $ terms st,
                  phase = phase st + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, proj2 bv) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, proj2 bv), theta)
 
{- The Phase folding analysis -}
applyGateExist :: (Primitive, Loc) -> State ExtCtx ()
applyGateExist (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \bv -> setSt v (bv .+. inj 0)
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

{- Run the analysis on a circuit and state -}
runCircuitExist :: [Primitive] -> ExtCtx -> ExtCtx
runCircuitExist circ = execState (mapM_ applyGateExist $ zip circ [2..])

{- Generates an initial state -}
initialState :: Parity parity => [ID] -> [ID] -> Ctx parity
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = zip (inputs ++ (vars \\ inputs)) [(inj x) | x <- [1..]]

{- Existential-style analysis -}
phaseAnalysisExist :: Analyzer
phaseAnalysisExist vars inputs circ =
  let result = runCircuitExist circ $ initialState vars inputs in
    ((snd . unzip . Map.toList $ terms result) ++ (orphans result), phase result)

{- Existential version -}
phaseFoldExist = phaseFoldGen phaseAnalysisExist

{- The Phase folding analysis -}
applyGate :: Parity parity => (Primitive, Loc) -> State (Ctx parity) ()
applyGate (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \bv -> setSt v (bv .+. inj 0)
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
    mapM_ (\v -> increaseDim >>= \k -> setSt v $ inj k) args

type IntCtx = Ctx IntSet

{- Run the analysis on a circuit and state -}
runCircuitInt :: [Primitive] -> IntCtx -> IntCtx
runCircuitInt circ = execState (mapM_ applyGate $ zip circ [2..])

{- Existential-style analysis -}
phaseAnalysisInt :: Analyzer
phaseAnalysisInt vars inputs circ =
  let result = runCircuitInt circ $ initialState vars inputs in
    ((snd . unzip . Map.toList $ terms result), phase result)

{- Existential version -}
phaseFold = phaseFoldGen phaseAnalysisInt

{- Run the analysis on a circuit and state -}
runCircuitf2 :: [Primitive] -> ExtCtx -> ExtCtx
runCircuitf2 circ = execState (mapM_ applyGate $ zip circ [2..])

{- Existential-style analysis -}
phaseAnalysisf2 :: Analyzer
phaseAnalysisf2 vars inputs circ =
  let result = runCircuitf2 circ $ initialState vars inputs in
    ((snd . unzip . Map.toList $ terms result), phase result)

{- Existential version -}
phaseFoldf2 = phaseFoldGen phaseAnalysisf2
