
module Specs.GraphSpec where

import Data.Bits (Bits (..))
import Data.Foldable (foldl')
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Set (Set)
import Data.Set qualified as Set
import Feynman.Algebra.Base (dMod2)
import Feynman.Control
import Feynman.Core
import Feynman.Graph
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Synthesis.Pathsum.Util
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

instance CircuitGate ExtractionGates where
  type GateQubit ExtractionGates = ID

  foldGateReferences f a (Hadamard xID) = f a xID
  foldGateReferences f a (MCT xIDs yID) = f (foldl' f a xIDs) yID
  foldGateReferences f a (Phase theta xIDs) = foldl' f a xIDs
  foldGateReferences f a (Swapper xID yID) = f (f a xID) yID

  mapGateReferences f (Hadamard xID) = Hadamard (f xID)
  mapGateReferences f (MCT xIDs yID) = MCT (map f xIDs) (f yID)
  mapGateReferences f (Phase theta xIDs) = Phase theta (map f xIDs)
  mapGateReferences f (Swapper xID yID) = Swapper (f xID) (f yID)

-- | Generates a random circuit
generateExtractionGates :: Int -> Int -> Int -> Gen [ExtractionGates]
generateExtractionGates m n k =
  resize k $ listOf1 $ oneof [genHadamard, genMCT, genPhase, genSwapper]
  where
    genHadamard = do
      x <- chooseInt (0, n)
      return $ Hadamard (q x)
    genMCT = do
      yxs <- genQubitParams
      let y : xs = yxs
      return $ MCT xs y
    genPhase = do
      xs <- genQubitParams
      theta <- genDMod2
      return $ Phase theta xs
    genSwapper = do
      x <- chooseInt (0, n)
      y <- chooseInt (0, n) `suchThat` (/= x)
      return $ Swapper (q x) (q y)
    genDMod2 = do
      x <- chooseInt (0, (1 `shiftL` m) - 2)
      return $ dMod2 (fromIntegral (x + 1)) m
    genQubitParams = genQubitParamsFrom IntSet.empty
    genQubitParamsFrom s = do
      -- starting from IntSet.empty should guarantee at least 1 entry
      i <- chooseInt (0, n) `suchThat` (`IntSet.notMember` s)
      rest <- oneof [return [], genQubitParamsFrom (IntSet.insert i s)]
      return $ q i : rest
    q idx = 'q' : show idx
    allQubitIdxSet = IntSet.fromAscList [0 .. n]

prop_ReknitUnravelIsIdentity :: (HasFeynmanControl) => Gen Bool
prop_ReknitUnravelIsIdentity = do
  circ <- generateExtractionGates 3 9 99
  denied <- sublistOf circ
  let inouts = Set.toList (circuitReferenceSet circ)
      deniedSet = Set.fromList denied
      (unCirc, stitches, _) = unravel (`Set.member` deniedSet) inouts circ
      reCirc = reknit unCirc stitches
  return $ equivalentToTrivialReorder circ reCirc

spec :: Spec
spec = do
  let ?feynmanControl =
        defaultControl
          { fcfTrace_Graph = False
          }
  prop "reknit . unravel is identity up to trivial reorder" prop_ReknitUnravelIsIdentity
  
-- main :: IO ()
-- main = do
--   let ?feynmanControl =
--         defaultControl
--           { fcfTrace_Graph = True
--           }
--   putStrLn "Unraveling [Primitive]:"
--   let (unr1, unr1Rej, _) =
--         unravel
--           (\g -> case g of H _ -> False; _ -> True)
--           ['@' : show n | n <- [1 ..]]
--           [ Uninterp "tof" ["a", "b", "c"],
--             H "c",
--             Uninterp "tof" ["a", "b", "c"],
--             H "c",
--             Uninterp "tof" ["a", "b", "c"],
--             H "c",
--             CNOT "c" "b"
--           ]
--   print unr1
--   print unr1Rej

--   let unr1Reknit = reknit unr1 unr1Rej
--   print unr1Reknit

--   putStrLn ""

--   putStrLn "Unraveling [ExtractionGates]:"
--   let (unr2, unr2Rej, _) =
--         unravel
--           (\g -> case g of Hadamard _ -> False; _ -> True)
--           ['@' : show n | n <- [1 ..]]
--           [ MCT ["a", "b"] "c",
--             Hadamard "c",
--             MCT ["a", "b"] "c",
--             Hadamard "c",
--             MCT ["a", "b"] "c",
--             Hadamard "c",
--             MCT ["c"] "b"
--           ]
--   print unr2
--   print unr2Rej

--   let unr2Reknit = reknit unr2 unr2Rej
--   print unr2Reknit

--   return ()

