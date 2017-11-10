module Optimization.TPar where

import Data.List hiding (transpose)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Graph.Inductive as Graph
import Data.Graph.Inductive.Query.DFS

import Data.Bits

import Debug.Trace


import Core
import Algebra.Base
import Algebra.Linear
import Algebra.Matroid
import Synthesis.Phase
import Synthesis.Reversible
import Synthesis.Reversible.Parallel
import Synthesis.Reversible.Gray

{-- Generalized T-par -}
{-  The idea is to traverse the circuit, tracking the phases,
    and whenever a Hadamard (or more generally something that
    maps a computational basis state to either a non-computational
    basis state or a probabilistic mixture, i.e. measurement)
    is applied synthesize a circuit for the phases that are no
    longer in the state space. Synthesis can proceed by either
    T-depth optimal matroid partitioning or CNOT-optimal ways -}
       
{- TODO: Merge with phase folding eventually -}

data AnalysisState = SOP {
  dim     :: Int,
  ivals   :: Map ID (F2Vec, Bool),
  qvals   :: Map ID (F2Vec, Bool),
  terms   :: Map F2Vec Angle,
  phase   :: Angle
} deriving Show

type Analysis = State AnalysisState

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> Analysis (F2Vec, Bool)
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ivals = ivals', qvals = qvals' }
                  return (bv', False)
      where dim' = dim st + 1
            bv' = bitI dim' (dim' - 1)
            ivals' = Map.insert v (bv', False) (ivals st)
            qvals' = Map.insert v (bv', False) (qvals st)

{- exists removes a variable (existentially quantifies it) then
 - orphans all terms that are no longer in the linear span of the
 - remaining variable states and assigns the quantified variable
 - a fresh (linearly independent) state -}
exists :: ID -> AnalysisState -> Analysis [(F2Vec, Angle)]
exists v st@(SOP dim ivals qvals terms phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v qvals
      (vecs, cnsts) = unzip avecs
      (terms', orp) = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = zip vecs' $ cnsts ++ [False]
      extendTerms   = Map.mapKeysMonotonic (zeroExtend 1)
      terms''       = if dim' > dim then extendTerms terms' else terms'
      vals          = Map.fromList $ zip (vars ++ [v]) avecs'
  in do
    put $ SOP dim' vals vals terms'' phase
    return $ Map.toList orp

replaceIval :: Map ID (F2Vec, Bool) -> AnalysisState -> AnalysisState
replaceIval ivals' st = st { ivals = ivals' }

updateQval :: ID -> (F2Vec, Bool) -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

addTerm :: (F2Vec, Bool) -> Angle -> AnalysisState -> AnalysisState
addTerm (bv, p) i st =
  case p of
    False -> st { terms = Map.alter (f i) bv $ terms st }
    True ->
      let terms' = Map.alter (f (-i)) bv $ terms st
          phase' = phase st + i
      in
        st { terms = terms', phase = phase' }
  where f i oldt = case oldt of
          Just x  -> Just $ x + i
          Nothing -> Just $ i
 
{-- The main analysis -}
applyGate :: AffineSynthesizer -> [Primitive] -> Primitive -> Analysis [Primitive]
applyGate synth gates g = case g of
  T v      -> do
    bv <- getSt v
    modify $ addTerm bv (Discrete $ dyadic 1 3)
    return gates
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (Discrete $ dyadic 7 3)
    return gates
  S v      -> do
    bv <- getSt v
    modify $ addTerm bv (Discrete $ dyadic 1 2)
    return gates
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (Discrete $ dyadic 3 2)
    return gates
  Z v      -> do
    bv <- getSt v
    modify $ addTerm bv (Discrete $ dyadic 1 1)
    return gates
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
    return gates
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
    return gates
  H v      -> do
    bv <- getSt v
    st <- get
    orphans <- exists v st
    return $ gates ++ synth (ivals st) (qvals st) orphans ++ [H v]
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
    return gates
  Rz p v -> do
    bv <- getSt v
    modify $ addTerm bv p
    return gates
  Rx p v -> do
    bv <- getSt v
    st <- get
    orphans <- exists v st
    return $ gates ++ synth (ivals st) (qvals st) orphans ++ [Rx p v]
  Ry p v -> do
    bv <- getSt v
    st <- get
    orphans <- exists v st
    return $ gates ++ synth (ivals st) (qvals st) orphans ++ [Ry p v]

applyGateOpen :: AffineOpenSynthesizer -> [Primitive] -> Primitive -> Analysis [Primitive]
applyGateOpen synth gates g = case g of
  T v      -> do
    bv <- getSt v
    modify $ addTerm bv 1
    return gates
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm bv 7
    return gates
  S v      -> do
    bv <- getSt v
    modify $ addTerm bv 2
    return gates
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm bv 6
    return gates
  Z v      -> do
    bv <- getSt v
    modify $ addTerm bv 4
    return gates
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
    return gates
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
    return gates
  H v      -> do
    bv <- getSt v
    st <- get
    orphans <- exists v st
    let (out, parities)    = synth (ivals st) orphans
        (out', correction) = unifyAffine v out (qvals st)
    st' <- get
    let out'' = if (dim st') > (dim st) then Map.map (\(bv, b) -> (zeroExtend 1 bv, b)) out' else out'
    modify $ replaceIval (Map.insert v ((qvals st')!v) out'')
    return $ gates ++ parities ++ correction ++ [H v]
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
    return gates

finalize :: AffineSynthesizer -> [Primitive] -> Analysis [Primitive]
finalize synth gates = do
  st <- get
  return $ gates ++ (synth (ivals st) (qvals st) $ Map.toList (terms st))

finalizeOpen :: AffineOpenSynthesizer -> [Primitive] -> Analysis [Primitive]
finalizeOpen synth gates = do
  st <- get
  let (out', parities) = synth (ivals st) $ Map.toList (terms st)
  return $ gates ++ parities ++ ((affineTrans linearSynth) out' (qvals st) [])
    
gtpar :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtpar osynth vars inputs gates =
  let synth = affineTrans osynth
      init = 
        SOP { dim = dim', 
              ivals = Map.fromList ivals, 
              qvals = Map.fromList ivals, 
              terms = Map.empty,
              phase = 0 }
  in
    evalState (foldM (applyGate synth) [] gates >>= finalize synth) init
  where dim'    = length inputs
        bitvecs = [(bitI dim' x, False) | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

gtparopen :: OpenSynthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtparopen osynth vars inputs gates =
  let synth = affineTransOpen osynth
      init = 
        SOP { dim = dim', 
              ivals = Map.fromList ivals, 
              qvals = Map.fromList ivals, 
              terms = Map.empty,
              phase = 0 }
  in
    evalState (foldM (applyGateOpen synth) [] gates >>= finalizeOpen synth) init
  where dim'    = length inputs
        bitvecs = [(bitI dim' x, False) | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

-- Optimization algorithms

{- t-par: the t-par algorithm from [AMM2014] (temporarily out of order) -}
tpar _ _ = id -- gtpar tparMore

{- minCNOT: CNOT minimization algorithm -}
minCNOT = gtparopen cnotMinGrayOpen
