module Feynman.Synthesis.Reversible.Allocation.ComputeFirst
  ( computeFirstAllocate,
  )
where

import Data.Foldable (foldl')
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Feynman.Synthesis.Reversible.Allocation

computeFirstAllocate :: AllocationProblem -> [Computation]
computeFirstAllocate = undefined

-- Our specification leads to a slightly relaxed game compared to what's
-- generally described as the reversible pebbling game in the literature, but
-- I think it still give us a correct algorithm.

-- copyCs and singleCs are expected to be complete, meaning:
-- - copyCs should have an entry for every possible computation
-- - singleCs should be derived from a computation DAG, and given unbounded
--   ancillas it should be possible to compute everything in the graph by
--   going through it in topological order (with the caveat that some
--   computation steps might need to be repeated where previous results get
--   consumed by later steps)
data ComputeFirstSpecification
  = CFS
  { problem :: AllocationProblem,
    -- copyCs are computations that duplicate exactly one specific result, and
    -- consume ancillas with no other dependencies
    copyCs :: Map ComputedResult [(Computation, [ComputedResult], [ComputedResult])],
    -- singleCs are computations that produce exactly one specific new result,
    -- but may consume anything
    singleCs :: Map ComputedResult [(Computation, [ComputedResult], [ComputedResult])]
  }

ensureComputed :: ComputeFirstSpecification -> ComputedResult -> ComputationState -> [Computation] -> (ComputationState, [Computation])
ensureComputed spec res state stepsRev
  -- already computed?
  | isComputed res state = (state, stepsRev)
  -- compute
  | otherwise = foldl' (\(a, b) c -> ensureComputed spec c a b) (state, stepsRev) []
  where
    p = problem spec
    fwd = singleCs spec ! res :: [(Computation, [ComputedResult], [ComputedResult])]

ensureUncomputed :: ComputeFirstSpecification -> ComputationState -> ComputedResult -> [Computation] -> [Computation]
ensureUncomputed = undefined
