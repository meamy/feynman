module Feynman.Optimization.PhaseFold where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase

import Data.List hiding (transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict

import Data.Graph.Inductive as Graph
import Data.Graph.Inductive.Query.DFS

import Data.Bits

{-- Phase folding optimization -}
{- We have two options for implementation here:
 -
 -  1. Maintain a current state of each qubit
 -     over the standard basis. When a Hadamard
 -     gate is applied we then need to write all
 -     phases over the new standard basis.
 -     Cost: 1 XOR per CNOT,
 -           n^2 + n*num keys XORs per H
 -
 -  2. Express each phase as XORs over the current
 -     value of the qubits. Need some way to ensure
 -     the current values of all qubits forms a
 -     basis, otherwise might miss some collisions.
 -     Could map qubit IDs with unique values to unique
 -     indices. On application of a Hadamard we then
 -     only need to remove any phase with a 1 at the
 -     location the Hadamard was applied. Every CNOT
 -     triggers an update of all phases though
 -     Cost: num keys XORs/conditional bit flips per CNOT, 
 -           num keys bit tests per H -} 

data AnalysisState = SOP {
  dim     :: Int,
  qvals   :: Map ID (F2Vec, Bool),
  terms   :: Map F2Vec (Set (Loc, Bool), Angle),
  orphans :: [(Set (Loc, Bool), Angle)],
  phase   :: Angle
} deriving Show

type Analysis = State AnalysisState

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> Analysis (F2Vec, Bool)
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', qvals = qvals' }
                  return (bv', False)
      where dim' = dim st + 1
            bv' = bitI dim' (dim' - 1)
            qvals' = Map.insert v (bv', False) (qvals st)

{- exists removes a variable (existentially quantifies it) then
 - orphans all terms that are no longer in the linear span of the
 - remaining variable states and assigns the quantified variable
 - a fresh (linearly independent) state -}
exists :: ID -> AnalysisState -> AnalysisState
exists v st@(SOP dim qvals terms orphans phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v qvals
      (vecs, cnsts) = unzip avecs
      (terms', orp) = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = zip vecs' $ cnsts ++ [False]
      orphans'      = (snd $ unzip $ Map.toList orp) ++ orphans
      extendTerms   = Map.mapKeysMonotonic (zeroExtend 1)
  in
    if dim' > dim
    then SOP dim' (Map.fromList $ zip (vars ++ [v]) avecs') (extendTerms terms') orphans' phase
    else SOP dim' (Map.fromList $ zip (vars ++ [v]) avecs') terms' orphans' phase

updateQval :: ID -> (F2Vec, Bool) -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

addTerm :: Loc -> (F2Vec, Bool) -> Angle -> AnalysisState -> AnalysisState
addTerm l (bv, p) i st =
  case p of
    False -> st { terms = Map.alter (f i) bv $ terms st }
    True  ->
      let terms' = Map.alter (f (-i)) bv $ terms st
          phase' = phase st + i
      in
        st { terms = terms', phase = phase' }
  where f i oldt = case oldt of
          Just (s, x) -> Just (Set.insert (l, p) s, x + i)
          Nothing     -> Just (Set.singleton (l, p), i)
 
{-- The main analysis -}
applyGate :: (Primitive, Loc) -> Analysis ()
applyGate (gate, l) = case gate of
  T v      -> do
    bv <- getSt v
    modify $ addTerm l bv (Discrete $ dyadic 1 3)
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm l bv (Discrete $ dyadic 7 3)
  S v      -> do
    bv <- getSt v
    modify $ addTerm l bv (Discrete $ dyadic 1 2)
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm l bv (Discrete $ dyadic 3 2)
  Z v      -> do
    bv <- getSt v
    modify $ addTerm l bv (Discrete $ dyadic 1 1)
  Rz p v -> do
    bv <- getSt v
    modify $ addTerm l bv p
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    mapM_ (\v -> modify $ exists v) args
  
runAnalysis :: [ID] -> [ID] -> [Primitive] -> AnalysisState
runAnalysis vars inputs gates =
  let init = 
        SOP { dim     = dim', 
              qvals   = Map.fromList ivals, 
              terms   = Map.empty,
              orphans = [],
              phase   = 0}
  in
    execState (mapM_ applyGate $ zip gates [2..]) init
  where dim'    = length inputs
        bitvecs = [(bitI dim' x, False) | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

phaseFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFold vars inputs gates =
  let (SOP _ _ terms orphans phase) = runAnalysis vars inputs gates
      allTerms      = (snd . unzip . Map.toList $ terms) ++ orphans
      (lmap, phase') =
        let f (lmap, phase) (locs, exp) =
              let (i, phase', exp') = case Set.findMax locs of
                    (i, False) -> (i, phase, exp)
                    (i, True)  -> (i, phase + exp, (-exp))
              in
                (Set.foldr (\(j, _) -> Map.insert j (if i == j then exp' else zero)) lmap locs, phase')
        in
          foldl' f (Map.empty, phase) allTerms
      gates' =
        let getTarget gate = case gate of
              T x    -> x
              S x    -> x
              Z x    -> x
              Tinv x -> x
              Sinv x -> x
              Rz _ x -> x
            f (gate, i) = case Map.lookup i lmap of
              Nothing -> [(gate, i)]
              Just exp
                | exp == zero -> []
                | otherwise   -> zip (synthesizePhase (getTarget gate) exp) (repeat i)
        in
          concatMap f (zip gates [2..])
  in
    (fst $ unzip $ gates') ++ (globalPhase (head vars) phase')
