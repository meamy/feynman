module Feynman.Optimization.HPhaseFold where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase

import Data.List hiding (transpose)
import Data.Maybe

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict

import Data.Bits

{-- Hadamard-conjugated Phase folding -}
{- Main idea here is to enable some propagation of
   phases through Hadamard gates by tracking
   conjugation contexts -}

data AnalysisState = SOP {
  dim     :: Int,
  qvals   :: Map ID (F2Vec, Bool),
  terms   :: Map F2Vec (Set (Loc, Bool), Angle),
  phase   :: Angle,
  subs    :: Map Int (F2Vec, Bool)
} deriving Show

type Analysis = State AnalysisState

assignFresh :: ID -> Analysis (Int, (F2Vec, Bool))
assignFresh v = get >>= \st ->
  let dim'   = dim st + 1
      bv'    = (bitI dim' (dim' - 1), False)
      qvals' = Map.insert v bv' (qvals st)
      terms' = Map.mapKeysMonotonic (zeroExtend 1) (terms st)
  in do
    put $ st { dim = dim', qvals = qvals', terms = terms' }
    return (dim' - 1, bv')

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> Analysis (F2Vec, Bool)
getSt v = get >>= \st ->
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> liftM snd $ assignFresh v

{- Here we want to compute the new state if interference has occurred,
   or otherwise assign a fresh variable with branch point the old state -}
existsH :: ID -> Analysis ()
existsH v = do
  input  <- getSt v
  (n, _) <- assignFresh v
  modify $ \st -> st { subs = Map.insert n input (subs st) }

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
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
  H v      -> do
    bv <- getSt v
    existsH v
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
  Rz p v -> do
    bv <- getSt v
    modify $ addTerm l bv p
  _      -> undefined
  
runAnalysis :: [ID] -> [ID] -> [Primitive] -> AnalysisState
runAnalysis vars inputs gates =
  let init = 
        SOP { dim     = dim', 
              qvals   = Map.fromList ivals, 
              terms   = Map.empty,
              phase   = 0,
              subs    = Map.empty }
  in
    execState (mapM_ applyGate $ zip gates [2..]) init
  where dim'    = length inputs
        bitvecs = [(bitI dim' x, False) | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs

hPhaseFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
hPhaseFold vars inputs gates =
  let (SOP _ _ terms phase subs) = runAnalysis vars inputs gates
      (lmap, phase') =
        let f (lmap, phase) (locs, exp) =
              let (i, phase', exp') = case Set.findMax locs of
                    (i, False) -> (i, phase, exp)
                    (i, True)  -> (i, phase + exp, (-exp))
              in
                (Set.foldr (\(j, _) -> Map.insert j (if i == j then exp' else zero)) lmap locs, phase')
        in
          foldl' f (Map.empty, phase) (Map.elems terms)
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
