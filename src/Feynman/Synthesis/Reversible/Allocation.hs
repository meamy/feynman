module Feynman.Synthesis.Reversible.Allocation where

import Control.Exception (assert)
import Data.Bifunctor (first)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntMultiSet (IntMultiSet)
import Data.IntMultiSet qualified as IntMultiSet
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Tuple (swap)
import Feynman.Synthesis.XAG.Graph qualified as XAG

newtype Computation = C Int deriving (Eq, Ord, Show)

newtype ComputedResult = CR Int deriving (Eq, Ord, Show)

newtype Resource = R Int deriving (Eq, Ord, Show)

zeroAncilla = CR 0

freshResults = [CR i | i <- [1 ..]]

freshComputations = [C i | i <- [1 ..]]

reverseComputation (C cid) = C (-cid)

isComputationReversed (C cid) = cid < 0

newtype ComputedResultBag = CRB IntMultiSet deriving (Eq, Ord, Show)

data AllocationProblem = AllocationProblem
  { computations :: IntMap (ComputedResultBag, ComputedResultBag),
    requiredResults :: ComputedResultBag,
    permittedResults :: ComputedResultBag,
    initialState :: ComputationState
  }

newtype ComputationState = CS IntMultiSet deriving (Eq, Ord, Show)

unC (C i) = i

unCR (CR i) = i

unCRB (CRB ms) = ms

unCS (CS ms) = ms

emptyResults = CRB IntMultiSet.empty

computationEffectsToList :: AllocationProblem -> [(Computation, (ComputedResultBag, ComputedResultBag))]
computationEffectsToList p = map (first C) (IntMap.toList (computations p))

problemFrom ::
  [(Computation, (ComputedResultBag, ComputedResultBag))] ->
  [ComputedResult] ->
  [ComputedResult] ->
  [ComputedResult] ->
  AllocationProblem
problemFrom effects required permitted initial =
  AllocationProblem
    { computations = IntMap.fromList (map (first unC) effects),
      requiredResults = CRB (IntMultiSet.fromList (map unCR required)),
      permittedResults = CRB (IntMultiSet.fromList allPermittedI),
      initialState = CS (IntMultiSet.fromList (map unCR initial))
    }
  where
    allPermittedI = Set.toList . Set.fromList . map unCR $ required ++ permitted

computationEffects :: AllocationProblem -> Computation -> (ComputedResultBag, ComputedResultBag)
computationEffects p (C ci)
  | ci < 0 = swap (findEffects (-ci))
  | otherwise = findEffects ci
  where
    findEffects i =
      assert (IntMap.member i (computations p)) $
        computations p IntMap.! i

resultsToSet :: ComputedResultBag -> Set ComputedResult
resultsToSet = Set.fromList . resultsToList

-- preserves occurrence counts
resultsToList :: ComputedResultBag -> [ComputedResult]
resultsToList (CRB bag) = map CR (IntMultiSet.toList bag)

-- preserves occurrence counts
resultsFromList :: [ComputedResult] -> ComputedResultBag
resultsFromList = CRB . IntMultiSet.fromList . map unCR

resultCount :: ComputedResult -> ComputedResultBag -> Int
resultCount (CR check) (CRB bag) = IntMultiSet.occur check bag

withoutAncillas :: ComputedResultBag -> ComputedResultBag
withoutAncillas (CRB bag) = CRB (IntMultiSet.deleteAll 0 bag)

withoutResults :: ComputedResultBag -> ComputedResultBag -> ComputedResultBag
withoutResults (CRB aBag) (CRB bBag) = CRB (aBag IntMultiSet.\\ bBag)

inBoth :: ComputedResultBag -> ComputedResultBag -> ComputedResultBag
inBoth (CRB aBag) (CRB bBag) = CRB (IntMultiSet.intersection aBag bBag)

stateToSet :: ComputationState -> Set ComputedResult
stateToSet = Set.fromList . stateToList

stateToList :: ComputationState -> [ComputedResult]
stateToList (CS state) = map CR (IntMultiSet.elems state)

hasAll :: ComputationState -> ComputedResultBag -> Bool
hasAll (CS has) (CRB needs) = (needs IntMultiSet.\\ has) == IntMultiSet.empty

afterApply :: ComputationState -> ComputedResultBag -> ComputedResultBag -> ComputedResultBag
afterApply (CS has) (CRB needs) (CRB yields) =
  CRB (IntMultiSet.union (has IntMultiSet.\\ needs) yields)

computedCount :: ComputedResult -> ComputationState -> Int
computedCount (CR check) (CS has) = IntMultiSet.occur check has

applyComputation :: AllocationProblem -> Computation -> ComputationState -> ComputationState
applyComputation p c (CS has) =
  assert (IntMultiSet.deleteAll 0 (needs IntMultiSet.\\ has) == IntMultiSet.empty) $
    CS (IntMultiSet.union (has IntMultiSet.\\ needs) yields)
  where
    (CRB needs, CRB yields) = computationEffects p c
