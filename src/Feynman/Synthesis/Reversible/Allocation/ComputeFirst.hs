module Feynman.Synthesis.Reversible.Allocation.ComputeFirst
  ( computeFirstAllocate,
  )
where

import Control.Exception (assert)
import Control.Monad (foldM)
import Control.Monad.State.Strict
import Data.Bifunctor (second)
import Data.Foldable (foldl')
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set, (\\))
import Data.Set qualified as Set
import Debug.Trace (trace)
import Feynman.Synthesis.Reversible.Allocation

-- Conditions required by this allocation strategy:
-- 1. there must be computations in the problem sufficient to meet the
--    requirements the copyCs and singleCs in the CFS
-- 2. all the initialResults must be in the permittedResults

computeFirstAllocate :: AllocationProblem -> Maybe [Computation]
computeFirstAllocate p =
  -- trace (" " ++ show ()) $
  trace ("cfprob copyCs " ++ show (copyCs cfprob)) $
    trace ("cfprob singleCs " ++ show (singleCs cfprob)) $
      trace ("prob computations " ++ show (computations p)) $
        trace ("prob permittedResults " ++ show (permittedResults p)) $
          trace ("prob requiredResults " ++ show (requiredResults p)) $
            trace ("prob initialState " ++ show (initialState p)) $
              ensureComputedCounts
                cfprob
                Set.empty
                (requiredResults p)
                emptyResults
                (CFS (initialState p) [])
                >>= (Just . reverse . stepsRev)
  where
    cfprob =
      CFP
        { problem = p,
          copyCs = filteredEffects asCopyEffect,
          singleCs = filteredEffects asSingleEffect
        }
    filteredEffects f =
      Map.fromList . mapMaybe (uncurry f) . computationEffectsToList $ p
    -- a copy effect duplicates one specific result using only ancillas
    asCopyEffect c (needs, yields)
      | length nl == 1, yl == [nlh, nlh] = Just (nlh, c)
      | otherwise = Nothing
      where
        nl = resultsToList (withoutAncillas needs)
        yl = resultsToList yields
        nlh = head nl
    -- a single effect produces exactly one new result
    asSingleEffect c (needs, yields)
      | length gainedl == 1 = Just (gainedh, c)
      | otherwise = Nothing
      where
        gainedl = resultsToList (withoutAncillas (withoutResults yields needs))
        gainedh = head gainedl

-- ComputeFirst, because first we compute everything we want, then we
-- uncompute the things we don't want.

-- Our specification leads to a slightly relaxed game compared to what's
-- generally described as the reversible pebbling game in the literature, but
-- I think it still give us a correct algorithm.

-- copyCs and singleCs are expected to be complete, meaning:
-- - copyCs should minimally have an entry for every result that can be
--   incidentally consumed by a computation that produces some other result
-- - singleCs should be derived from a computation DAG, and given unbounded
--   ancillas it should be possible to compute everything in the graph by
--   going through it in topological order (with the caveat that some
--   computation steps might need to be repeated where previous results get
--   consumed by later steps)
data ComputeFirstProblem
  = CFP
  { problem :: AllocationProblem,
    -- copyCs are computations that duplicate exactly one specific result, and
    -- consume ancillas with no other dependencies; note that inverted, these
    -- can uncopy and return extra outputs to 0
    copyCs :: Map ComputedResult Computation,
    -- singleCs are computations that produce exactly one specific new result,
    -- but may consume anything
    singleCs :: Map ComputedResult Computation
  }

data ComputeFirstState
  = CFS
  { cmptState :: ComputationState,
    stepsRev :: [Computation]
  }

addStep :: ComputeFirstProblem -> Computation -> ComputeFirstState -> Maybe ComputeFirstState
addStep cfprob c s@(CFS {cmptState = cs, stepsRev = sr})
  | withoutAncillas (missingFrom cs needs) == emptyResults =
      Just (s {cmptState = applyComputation (problem cfprob) c cs, stepsRev = c : sr})
  | otherwise = Nothing
  where
    (needs, yields) = computationEffects (problem cfprob) c

ensureComputedCounts :: ComputeFirstProblem -> Set ComputedResult -> ComputedResultBag -> ComputedResultBag -> ComputeFirstState -> Maybe ComputeFirstState
ensureComputedCounts cfprob wantSet needs yields st =
  -- insert dups to satisfy needs counts, wantAndWillLose
  -- we must already have at least one of everything we need
  foldM (flip (ensureComputedAtAll cfprob depWantSet)) st (resultsToSet needs)
    >>= adjustComputedCounts
  where
    depWantSet = Set.union wantSet (resultsToSet needs)
    adjustComputedCounts st' =
      assert ((resultsToSet needs \\ haveSet) == Set.empty) $
        foldM
          ( \s r ->
              if Map.member r (copyCs cfprob)
                then addStep cfprob (copyCs cfprob ! r) s
                else trace ("need to duplicate " ++ show r ++ " but can't") Nothing
          )
          st'
          (filter (/= zeroAncilla) (wantAndWillLose ++ needsDupList))
      where
        -- in the event some computation needs multiple of the same result, we
        -- may need to duplicate it since we only ensured there was at least 1
        needsDupList =
          concatMap (uncurry replicate)
            . filter ((> 0) . fst)
            . map (\r -> (resultCount r needs - computedCount r (cmptState st'), r))
            . Set.toList
            . resultsToSet
            $ needs
        -- things we have, that we want to keep, that we will lose (unless we
        -- duplicate them an extra time)
        -- we use sets because the multiplicity isn't important, in fact we
        -- would prefer to duplicate things just before they're actually
        -- needed to minimize qubit use
        wantAndWillLose = Set.toList (wantAndHave \\ willHave)
        willHave = resultsToSet (afterApply (cmptState st') needs yields)
        wantAndHave = Set.intersection haveSet wantSet
        haveSet = stateToSet (cmptState st')

ensureComputedAtAll :: ComputeFirstProblem -> Set ComputedResult -> ComputedResult -> ComputeFirstState -> Maybe ComputeFirstState
ensureComputedAtAll cfprob wantSet res st
  -- already computed?
  | computedCount res (cmptState st) > 0 = return st
  -- try computing each dependency
  | Map.member res (singleCs cfprob) =
      ensureComputedCounts cfprob wantSet (withoutAncillas needs) yields st
        >>= addStep cfprob cmpt
  | otherwise = trace ("need to compute " ++ show res ++ " but can't") Nothing
  where
    -- The computation that gets us res
    cmpt = singleCs cfprob ! res
    (needs, yields) = computationEffects (problem cfprob) cmpt

ensureUncomputed :: ComputeFirstProblem -> ComputationState -> ComputedResult -> [Computation] -> [Computation]
ensureUncomputed = undefined
