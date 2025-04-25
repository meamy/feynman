module Feynman.Synthesis.Reversible.XAG where

import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph qualified as XAG

{-

Synthesis:
1. take a boolean function and synthesize input-saving
2. take a pair of a boolean function and its inverse, and synthesize input-erasing

The parameters we can modulate are:
1. function (input) encoding
2. function (intermediate) optimization
3. ancilla use/allocation in transcoding to reversible

-}

-- returns ExtractionGates, unused ancilla names
-- inputNames and outputNames must be disjoint
inputSavingXAGSynth :: XAG.Graph -> [ID] -> [ID] -> [ID] -> ([ExtractionGates], [ID])
inputSavingXAGSynth funcXAG inputNames outputNames ancillaNames = undefined

-- returns ExtractionGates, unused ancilla names
inputErasingXAGSynth :: XAG.Graph -> XAG.Graph -> [ID] -> [ID] -> ([ExtractionGates], [ID])
inputErasingXAGSynth fwdXAG revXAG inoutNames ancillaNames =
  -- Add ancillas for input-saving outputs
  -- synthesize
  undefined
