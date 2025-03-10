module Specs.SynthesisReversibleAllocationSpec where

import Data.Foldable (foldl')
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (elemIndex)
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace (trace, traceM)
import Feynman.Control
import Feynman.Core
import Feynman.Optimization.Classical
import Specs.TestUtil
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

prop_MCTsReallocateEvalsEquivalent :: (HasFeynmanControl) => Gen Bool
prop_MCTsReallocateEvalsEquivalent = do
  mcts <- generateMCTs 5 99

  let allIDs = Set.toList . foldl' Set.union Set.empty . map (Set.fromList . mctIDs) $ mcts

      reallocation = reallocateQubits mcts allIDs allIDs idGen
      (resynthMCTs, inMap, outMap, _) = fromMaybe (error "reallocation failed") reallocation

      reInIDs = 
        trace ("inMap: " ++ show inMap) $ 
          trace ("outMap: " ++ show outMap) $ 
            map (Map.fromList inMap !) allIDs
      reOutIDs = map (Map.fromList outMap !) allIDs
  trace ("reInIDs: " ++ show reInIDs) $ return ()
  trace ("reOutIDs: " ++ show reOutIDs) $ return ()

  let tt = makeTruthTable (length allIDs)
      mctRes = map ((\m -> map (m !) allIDs) . Map.fromList . evalMCTs mcts . zip allIDs) tt
      resynthMCTRes = map ((\m -> map (m !) reOutIDs) . Map.fromList . evalMCTs mcts . zip reInIDs) tt

  return $              mctRes == resynthMCTRes

spec :: Spec
spec = do
  let ?feynmanControl = defaultControl {fcfTrace_Graph = True}
  prop "reallocateQubits produces equivalent MCTs" prop_MCTsReallocateEvalsEquivalent
