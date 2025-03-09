module Feynman.Synthesis.Reversible.Allocation.ComputeFirst
  ( computeFirstAllocate,
  )
where

import Control.Monad (foldM)
import Control.Monad.State.Strict
import Data.Foldable (foldl')
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.MultiMap qualified as MultiMap
import Data.Set (Set, (\\))
import Data.Set qualified as Set
import Feynman.Synthesis.Reversible.Allocation

-- Conditions required by this allocation strategy:
-- 1. there must be computations in the problem sufficient to meet the
--    requirements the copyCs and singleCs in the CFS
-- 2. all the initialResults must be in the permittedResults

computeFirstAllocate :: AllocationProblem -> Maybe [Computation]
computeFirstAllocate = undefined

-- ComputeFirst, because first we compute everything we want, then we
-- uncompute the things we don't want.

-- Our specification leads to a slightly relaxed game compared to what's
-- generally described as the reversible pebbling game in the literature, but
-- I think it still give us a correct algorithm.

-- copyCs and singleCs are expected to be complete, meaning:
-- - copyCs should have an entry for every result BESIDES the ones in the
--   problem's initialResults
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

addStep :: Computation -> ComputeFirstState -> Maybe ComputeFirstState
addStep c s@(CFS {stepsRev = sr}) = Just (s {stepsRev = c : sr})

ensureComputed :: ComputeFirstProblem -> ComputedResultBag -> ComputedResult -> ComputeFirstState -> Maybe ComputeFirstState
ensureComputed cfprob wantKeep res st
  -- already computed?
  | computedCount res (cmptState st) > 0 = return st
  -- try computing each dependency
  | unmetNeeds == emptyResults = computeResult
  | otherwise = ensureDependenciesAndRetry
  where
    -- The computation that gets us res
    cmpt = singleCs cfprob ! res
    (needs, yields) = head (computations (problem cfprob) MultiMap.! cmpt)
    unmetNeeds = missingFrom (cmptState st) needs

    computeResult = do
      -- insert dups to satisfy needs counts
      foldM (\s r -> addStep (copyCs cfprob ! r) s) st wantAndWillLose
      -- insert dups for wantAndWillLose
      -- insert computation
      -- insert annihilates to reduce counts not in wants
      return st
      where
        -- things we have, that we want to keep, that we will lose -- to be dup'd
        -- we use sets because the multiplicity isn't important, in fact we would
        -- prefer to duplicate things just before they're actually needed to
        -- minimize qubit use
        wantAndWillLose = Set.toList (wantAndHave Set.\\ willHave)
        willHave = resultsAsSet (afterApplication (cmptState st) needs yields)
        wantAndHave = resultsAsSet (alreadyHave (cmptState st) wantKeep)

    ensureDependenciesAndRetry =
      foldM (flip (ensureComputed cfprob depWants)) st []
        >>= ensureComputed cfprob wantKeep res
      where
        depWants = wantKeep

ensureUncomputed :: ComputeFirstProblem -> ComputationState -> ComputedResult -> [Computation] -> [Computation]
ensureUncomputed = undefined
