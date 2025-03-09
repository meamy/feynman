module Feynman.Synthesis.Reversible.Allocation where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.IntMultiSet (IntMultiSet, (\\))
import Data.IntMultiSet qualified as IntMultiSet
import Data.MultiMap (MultiMap)
import Data.MultiMap qualified as MultiMap
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Data.Maybe (fromMaybe)

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
  { computations :: MultiMap Computation (ComputedResultBag, ComputedResultBag),
    requiredResults :: ComputedResultBag,
    permittedResults :: ComputedResultBag,
    initialResults :: ComputedResultBag
  }

newtype ComputationState = CS IntMultiSet

unC (C i) = i
unCR (CR i) = i
unCRB (CRB ms) = ms
unCS (CS ms) = ms

emptyResults = CRB IntMultiSet.empty

resultsAsSet :: ComputedResultBag -> Set ComputedResult
resultsAsSet (CRB bag) = Set.fromList (map CR (IntMultiSet.elems bag))

missingFrom :: ComputationState -> ComputedResultBag -> ComputedResultBag
missingFrom (CS has) (CRB needs) = CRB (needs \\ has)

alreadyHave :: ComputationState -> ComputedResultBag -> ComputedResultBag
alreadyHave (CS has) (CRB needs) = CRB (IntMultiSet.intersection has needs)

inBoth :: ComputedResultBag -> ComputedResultBag -> ComputedResultBag
inBoth (CRB aBag) (CRB bBag) = CRB (IntMultiSet.intersection aBag bBag)

afterApplication :: ComputationState -> ComputedResultBag -> ComputedResultBag -> ComputedResultBag
afterApplication (CS has) (CRB needs) (CRB yields) = CRB ((has \\ needs) `IntMultiSet.union` yields)

canApply :: ComputationState -> ComputedResultBag -> Bool
canApply (CS has) (CRB needs) = (needs \\ has) == IntMultiSet.empty

resultBagFromList :: [ComputedResult] -> ComputedResultBag
resultBagFromList = CRB . IntMultiSet.fromList . map unCR

resultBagToList :: ComputedResultBag -> [ComputedResult]
resultBagToList = map CR . IntMultiSet.toList . unCRB

allComputed :: ComputedResultBag -> ComputationState -> Bool
allComputed (CRB wants) (CS has) = has `IntMultiSet.isSubsetOf` wants

computedCount :: ComputedResult -> ComputationState -> Int
computedCount (CR check) (CS has) = IntMultiSet.occur check has

addComputed :: ComputedResult -> ComputationState -> ComputationState
addComputed (CR got) (CS has) = CS (IntMultiSet.insert got has)

removeComputed :: ComputedResult -> ComputationState -> ComputationState
removeComputed (CR lost) (CS has) =CS (IntMultiSet.delete lost has)
