module Feynman.Synthesis.Reversible.Allocation where

import Data.IntMap.Strict (IntMap, (!))
import Data.IntMap.Strict qualified as IntMap
import Feynman.Synthesis.XAG.Graph qualified as XAG

newtype Computation = C Int deriving (Eq, Ord, Show)

newtype ComputedResult = CR Int deriving (Eq, Ord, Show)

newtype Resource = R Int deriving (Eq, Ord, Show)

zeroAncilla = CR 0

freshResults = [CR i | i <- [1 ..]]

freshComputations = [C i | i <- [1 ..]]

reverseComputation (C cid) = C (-cid)

isComputationReversed (C cid) = cid < 0

data AllocationProblem = AllocationProblem
  { computations :: [(Computation, [ComputedResult], [ComputedResult])],
    requiredResults :: [ComputedResult],
    permittedResults :: [ComputedResult],
    initialResults :: [ComputedResult]
  }

newtype ComputationState = CS (IntMap Int)

isComputed :: ComputedResult -> ComputationState -> Bool
isComputed (CR resI) (CS stateM) = IntMap.member resI stateM

addComputed :: ComputedResult -> ComputationState -> ComputationState
addComputed (CR resI) (CS stateM) = CS (IntMap.insertWith (+) resI 1 stateM)

removeComputed :: ComputedResult -> ComputationState -> ComputationState
removeComputed (CR resI) (CS stateM) =
  let updateF i
        | i > 1 = Just (i - 1)
        | otherwise = Nothing
   in CS (IntMap.update updateF resI stateM)
