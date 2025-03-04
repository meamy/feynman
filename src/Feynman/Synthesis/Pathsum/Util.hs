module Feynman.Synthesis.Pathsum.Util (ExtractionGates (..)) where

import Feynman.Algebra.Base
import Feynman.Core
import Feynman.Graph
import Data.Foldable (foldl')

data ExtractionGates = Hadamard ID | Phase DMod2 [ID] | MCT [ID] ID | Swapper ID ID deriving (Show, Eq, Ord)

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

