module Specs.SynthesisXAGUtilSpec where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (elemIndex)
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace (trace, traceM)
import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph (eval)
import Feynman.Synthesis.XAG.Util (fromMCTs, fromSBools)
import Specs.TestUtil
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

prop_XAGFromMCTsEvalsEquivalent :: (HasFeynmanControl) => Gen Bool
prop_XAGFromMCTsEvalsEquivalent = do
  mcts <- generateMCTs 5 99
  let (xag, inputIDs, outputIDs) = fromMCTs mcts
  let tt = makeTruthTable (length inputIDs)
      mctRes = map ((\m -> map (m !) outputIDs) . Map.fromList . evalMCTs mcts . zip inputIDs) tt
      -- I'm suspicious xagOutOrder works by accident and will fail if outputIDs actually get for real reordered
      xagOutOrder = mapMaybe (`elemIndex` outputIDs) inputIDs
      xagRes = map (\ins -> map (eval xag ins !!) xagOutOrder) tt
  return $ mctRes == xagRes

mctIDs :: ExtractionGates -> [ID]
mctIDs (MCT controls target) = target : controls
mctIDs gate = error (show gate ++ " in MCT list")

makeTruthTable :: (Eq t, Num t) => t -> [[Bool]]
makeTruthTable 0 = [[]]
makeTruthTable n = [b : moreB | b <- [False, True], moreB <- makeTruthTable (n - 1)]

spec :: Spec
spec = do
  let ?feynmanControl = defaultControl {fcfTrace_Graph = True}
  prop "fromMCTs produces equivalent XAG" prop_XAGFromMCTsEvalsEquivalent
