module Feynman.Synthesis.Pathsum.Util (ExtractionGates (..)) where

import Feynman.Algebra.Base
import Feynman.Core

data ExtractionGates = Hadamard ID | Phase DMod2 [ID] | MCT [ID] ID | Swapper ID ID deriving (Show, Eq, Ord)
