module Main (main) where

import Data.Foldable (foldl')
import Feynman.Control
import Feynman.Core
import Feynman.Graph
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Synthesis.Pathsum.Util
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

main :: IO ()
main = do
  let ?feynmanControl =
        defaultControl
          { fcfTrace_Graph = True
          }
  putStrLn "Unraveling [Primitive]:"
  let (unr1, unr1Rej, _) =
        unravel
          (\g -> case g of H _ -> False; _ -> True)
          ['@' : show n | n <- [1 ..]]
          [ Uninterp "tof" ["a", "b", "c"],
            H "c",
            Uninterp "tof" ["a", "b", "c"],
            H "c",
            Uninterp "tof" ["a", "b", "c"],
            H "c",
            CNOT "c" "b"
          ]
  print unr1
  print unr1Rej

  let unr1Reknit = reknit unr1 unr1Rej
  print unr1Reknit

  putStrLn ""

  putStrLn "Unraveling [ExtractionGates]:"
  let (unr2, unr2Rej, _) =
        unravel
          (\g -> case g of Hadamard _ -> False; _ -> True)
          ['@' : show n | n <- [1 ..]]
          [ MCT ["a", "b"] "c",
            Hadamard "c",
            MCT ["a", "b"] "c",
            Hadamard "c",
            MCT ["a", "b"] "c",
            Hadamard "c",
            MCT ["c"] "b"
          ]
  print unr2
  print unr2Rej

  let unr2Reknit = reknit unr2 unr2Rej
  print unr2Reknit

  return ()
