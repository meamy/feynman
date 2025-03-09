module Specs.SynthesisXAGUtilSpec where

import Data.Foldable (foldl')
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (elemIndex)
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Set (Set, (\\))
import Data.Set qualified as Set
import Debug.Trace (trace, traceM)
import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph (eval)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.Util (fromMCTs, fromSBools, toMCTs)
import Specs.TestUtil
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

prop_XAGFromMCTsEvalsEquivalent :: (HasFeynmanControl) => Gen Bool
prop_XAGFromMCTsEvalsEquivalent = do
  mcts <- generateMCTs 5 99

  let (xag, inIDs, outIDs) = fromMCTs mcts [] []

  let tt = makeTruthTable (length inIDs)

      mctRes = map ((\m -> map (m !) outIDs) . Map.fromList . evalMCTs mcts . zip inIDs) tt

      xagRes = map (eval xag) tt

  return $ mctRes == xagRes

prop_XAGToMCTsEvalsEquivalent :: (HasFeynmanControl) => Gen Bool
prop_XAGToMCTsEvalsEquivalent = do
  xag <- generateXAG

  let inOutIDs = [q i | i <- [1 .. max (length (XAG.inputIDs xag)) (length (XAG.outputIDs xag))]]
  inOutIDs' <- shuffle inOutIDs
  let inIDs = take (length (XAG.inputIDs xag)) inOutIDs'
      outIDs = take (length (XAG.outputIDs xag)) inOutIDs'

      (mcts, _) = toMCTs xag inIDs outIDs idGen
      allIDsSet = foldl' Set.union Set.empty . map (Set.fromList . mctIDs) $ mcts
      ancillaIDs = Set.toList (allIDsSet \\ Set.fromList inIDs)

      tt = makeTruthTable (length inIDs)

      mctRes =
        map
          ( (\m -> map (m !) outIDs)
              . Map.fromList
              . evalMCTs mcts
              . ([(a, False) | a <- ancillaIDs] ++)
              . zip inIDs
          )
          tt

      xagRes = map (eval xag) tt

  return $ mctRes == xagRes

mctIDs :: ExtractionGates -> [ID]
mctIDs (MCT controls target) = target : controls
mctIDs (Swapper x y) = [x, y]
mctIDs gate = error (show gate ++ " in MCT list")

makeTruthTable :: (Eq t, Num t) => t -> [[Bool]]
makeTruthTable 0 = [[]]
makeTruthTable n = [b : moreB | b <- [False, True], moreB <- makeTruthTable (n - 1)]

spec :: Spec
spec = do
  let ?feynmanControl = defaultControl {fcfTrace_Graph = True}
  prop "fromMCTs produces equivalent XAG" prop_XAGFromMCTsEvalsEquivalent
  prop "toMCTs produces equivalent MCTs" prop_XAGToMCTsEvalsEquivalent
