{-# LANGUAGE ScopedTypeVariables #-}

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
newtype Analysis repr = Analysis ([ID] -> [ID] -> [Primitive] -> ([Term], Angle))

{- Class of representations of affine parities -}
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
  

instance Parity F2Vec where
  a .+. b    = a + b
  split a    = (zeroExtend (-1) $ shiftR a 1, testBit a 0)
  comb (a,b) = if b then setBit a' 0 else a' where a' = (flip shiftL) 1 $ zeroExtend 1 a
  nil        = 0
  var i      = bitI (max 32 (i+1)) i

instance Parity IntSet where
  a .+. b    = symDiff a b
  split a    = (IntSet.delete 0 a, IntSet.member 0 a)
  comb (a,b) = if b then IntSet.insert 0 a else a
  nil        = IntSet.empty
  var i      = IntSet.singleton i

{- Symmetric difference implementation for int sets -}
symDiff :: IntSet -> IntSet -> IntSet
symDiff = IntSet.foldr (\k s -> c $ IntSet.alterF (fmap not . pure) k s) where
  c = coerce :: Identity IntSet -> IntSet

{-- Generic algorithm using arbitrary parity representations -}

data Ctx parity = Ctx {
  dim     :: Int,
  ket     :: Map ID parity,
  terms   :: Map parity Term,
  orphans :: [Term],
  phase   :: Angle
} deriving Show

{- Get the parity for variable v, or otherwise allocate one -}
getSt :: Parity parity => ID -> State (Ctx parity) (parity)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket' }
                  return (bv')
      where dim' = dim st + 1
            bv'  = var dim'
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

{- Adds a mergeable phase term -}
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
 
{- The Phase folding analysis -}
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

{- Generates an initial state -}
initialState :: Parity parity => [ID] -> [ID] -> Ctx parity
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = (zip inputs [(var x) | x <- [1..]]) ++ (zip (vars \\ inputs) [nil | x <- [1..]])

{- Run the analysis on a circuit and state -}
runCircuit :: Parity parity => [Primitive] -> Ctx parity -> Ctx parity
runCircuit circ = execState (mapM_ applyGate $ zip circ [2..])

{- Analysis for a particular parity representation -}
mkAnalyzer :: forall repr . Parity repr => Analysis repr
mkAnalyzer = Analysis (analysis)
  where analysis vars inputs circ =
          let result :: Ctx repr
              result = runCircuit circ $ initialState vars inputs
          in
            ((snd . unzip . Map.toList $ terms result), phase result)

{- Run the analysis and merge phase gates -}
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

{- Via int sets. Fast and sparse -}
phaseFold = phaseFoldGen (mkAnalyzer :: Analysis IntSet)

{- Via bitvectors. Faster but high memory -}
fastPhaseFold = phaseFoldGen (mkAnalyzer :: Analysis F2Vec)

{-- Existential quantifiction based -}
{-  Deprecated -}

type ExtCtx = Ctx F2Vec

{- Existentially quantifies a variable. In particular, any term that no
 - longer has a representative becomes an "orphan" -- a term with
 - no current representative -}
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

{- The Phase folding analysis -}
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

{- Run the analysis on a circuit and state -}
runCircuitAlt :: [Primitive] -> ExtCtx -> ExtCtx
runCircuitAlt circ = execState (mapM_ applyGateExist $ zip circ [2..])

{- Existential-style analysis -}
phaseAnalysisAlt :: Analysis ExtCtx
phaseAnalysisAlt = Analysis go where
  go vars inputs circ =
    let result = runCircuitAlt circ $ initialState vars inputs in
      ((snd . unzip . Map.toList $ terms result) ++ (orphans result), phase result)

{- Existential version -}
phaseFoldAlt = phaseFoldGen phaseAnalysisAlt
