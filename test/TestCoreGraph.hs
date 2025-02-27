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
  print
    ( unravel
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
    )

  putStrLn ""

  putStrLn "Unraveling [ExtractionGates]:"
  print
    ( unravel
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
    )

  return ()
