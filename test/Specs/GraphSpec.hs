module Specs.GraphSpec where

import Data.Bits (Bits (..))
import Data.Foldable (foldl')
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (intercalate, singleton)
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace
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
      return $ Phase 0 xs
    genSwapper = do
      x <- chooseInt (0, n)
      y <- chooseInt (0, n) `suchThat` (/= x)
      return $ Swapper (q x) (q y)
    genDMod2 = do
      x <- chooseInt (0, (1 `shiftL` m) - 2)
      return $ dMod2 (fromIntegral (x + 1)) m
    genQubitParams = do
      sz <- getSize
      let count = max 0 (min (sz - 1) n)
      rBits <- choose (0, (1 `shiftL` count) - 1) :: Gen Integer
      genQubitParamsAux (rBits .|. 1) allIdxs []
    -- using rBits as a random source, select
    genQubitParamsAux rBits elems qubits
      | even rBits = return qubits
      | otherwise = do
          i <- choose (0, length elems - 1)
          let (ls, e : rs) = splitAt i elems
          genQubitParamsAux (rBits `shiftR` 1) (ls ++ rs) (q e : qubits)
    q idx = 'q' : show idx
    allIdxs = [0 .. n]

pretty = concatMap (("\n" ++) . show)

indent n = unlines . map (replicate n ' ' ++) . lines

idGen = ['@' : show i | i <- [1 ..]]

prop_ReknitUnravelIsIdentity :: (HasFeynmanControl) => Gen Bool
prop_ReknitUnravelIsIdentity = do
  circ <- generateExtractionGates 3 19 99
  denied <- sublistOf circ
  let deniedSet = Set.fromList denied
      (unCirc, stitches, _) = unravel (`Set.member` deniedSet) idGen circ
      reCirc = reknit unCirc stitches
  return $ equivalentToTrivialReorder circ reCirc

spec :: Spec
spec = do
  let ?feynmanControl = defaultControl
  prop "reknit . unravel is identity up to trivial reorder" prop_ReknitUnravelIsIdentity

main :: IO ()
main = do
  let ?feynmanControl =
        defaultControl
          { fcfTrace_Graph = True
          }

  -- let circ =
  --       [ Phase 0 ["q4", "q9", "q0", "q5"], --
  --         Swapper "q3" "q5",
  --         Swapper "q3" "q9", --
  --         Hadamard "q3",
  --         Swapper "q7" "q3",
  --         Phase 0 ["q3", "q2", "q6"],
  --         MCT ["q5"] "q2", --
  --         MCT ["q3", "q2", "q7", "q9"] "q6",
  --         MCT ["q9", "q7", "q5", "q6", "q3", "q1"] "q8",
  --         Phase 0 ["q5"], --
  --         Swapper "q3" "q1",
  --         Phase 0 ["q3", "q0"],
  --         Phase 0 ["q5", "q7", "q1"], --
  --         Hadamard "q2",
  --         MCT [] "q5", --
  --         Phase 0 ["q4", "q3", "q5"], --
  --         MCT ["q6", "q9"] "q3", --
  --         Phase 0 ["q7"], --
  --         Phase 0 ["q8", "q4", "q7"], --
  --         MCT ["q5", "q6", "q7"] "q8",
  --         Phase 0 ["q2"],
  --         Phase 0 ["q1", "q3"]
  --       ]

  -- let deny =
  --       Set.fromList
  --         [ Phase 0 ["q4", "q9", "q0", "q5"],
  --           Swapper "q3" "q9",
  --           MCT ["q5"] "q2",
  --           Phase 0 ["q5"],
  --           Phase 0 ["q5", "q7", "q1"],
  --           MCT [] "q5",
  --           Phase 0 ["q4", "q3", "q5"],
  --           MCT ["q6", "q9"] "q3",
  --           Phase 0 ["q7"],
  --           Phase 0 ["q8", "q4", "q7"]
  --         ]
  -- let circ =
  --       [ Phase 0 ["q5"], --
  --         Swapper "q3" "q1",
  --         Phase 0 ["q3", "q0"], --
  --         Phase 0 ["q5", "q7", "q1"], --
  --         MCT [] "q5", --
  --         Swapper "q7" "q3",
  --         Phase 0 ["q1", "q3"]
  --       ]

  -- let deny =
  --       Set.fromList
  --         [ Phase 0 ["q5"],
  --           Phase 0 ["q3", "q0"],
  --           Phase 0 ["q5", "q7", "q1"],
  --           MCT [] "q5"
  --         ]

  let circ =
        [ MCT [] "q7", --
          Swapper "q2" "q5",
          Hadamard "q4",
          Hadamard "q9",
          Hadamard "q5",
          Swapper "q4" "q2", --
          Phase 0 ["q4", "q5"], --
          Hadamard "q1",
          Swapper "q4" "q0", --
          Phase 0 ["q0", "q6", "q2"], --
          MCT [] "q6",
          Swapper "q2" "q4", --
          Swapper "q0" "q3",
          Swapper "q7" "q9", --
          Phase 0 ["q3"]
        ]
  let deny =
        Set.fromList
          [ MCT [] "q7",
            Swapper "q4" "q2",
            Phase 0 ["q4", "q5"],
            Swapper "q4" "q0",
            Swapper "q2" "q4",
            Phase 0 ["q0", "q6", "q2"],
            Swapper "q7" "q9"
          ]

  let (unr1, unr1Rej, _) = unravel (`Set.notMember` deny) idGen circ

  putStrLn "Unraveling [ExtractionGates]:"
  putStrLn (indent 2 (pretty unr1))
  putStrLn (indent 2 (show unr1Rej))
  putStrLn ""
  putStrLn "Result:"
  let unr1Reknit = reknit unr1 unr1Rej
  putStrLn (indent 2 (pretty unr1Reknit))
  putStrLn ""
  putStrLn "Equivalent:"
  putStrLn (show $ equivalentToTrivialReorder circ unr1Reknit)

  return ()
