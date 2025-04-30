module Feynman.Synthesis.Reversible.XAG where

import Data.Maybe (fromMaybe)
import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.MinMultSat qualified as XAG
import Feynman.Synthesis.XAG.Simplify qualified as XAG
import Feynman.Synthesis.XAG.Util (toMCTs)

-- take a boolean function and synthesize input-saving
-- returns ExtractionGates, unused ancilla names
inputSavingXAGSynth :: (HasFeynmanControl) => XAG.Graph -> [ID] -> [ID] -> [ID] -> ([ExtractionGates], [ID])
inputSavingXAGSynth xag inputNames outputNames ancillaNames =
  (gates ++ zipWith (\q c -> MCT [q] c) rawOutNames copyNames, ancillaNames'')
  where
    (copyPrefix, ancillaNames') = (head ancillaNames, tail ancillaNames)
    copyNames = map (copyPrefix ++) inputNames
    (rawOutNames, gates, ancillaNames'') = toMCTs xag inputNames ancillaNames'

-- take a pair of a boolean function and its inverse, and synthesize input-erasing
-- returns ExtractionGates, unused ancilla names
inputErasingXAGSynth :: (HasFeynmanControl) => XAG.Graph -> XAG.Graph -> [ID] -> [ID] -> ([ExtractionGates], [ID])
inputErasingXAGSynth fwdXAG revXAG inoutNames ancillaNames =
  -- This synthesis builds on the input-saving one. Using that method, both
  -- computing the (forward) function into fresh qubits, and computing the
  -- reverse function into fresh qubits, yield the same result: input to and
  -- output of the function.
  -- We can exploit this to uncompute and erase the input, by uncomputing the
  -- reverse function after computing the forward one. This is the trick that
  -- people don't usually talk about, from section 3 of Bennett's 1989 paper.
  -- If you're into complexity, it's a footnote, sure -- just another constant
  -- linear factor -- but if you're doing practical synthesis as a step in a
  -- larger algorithm, it is critical to erase the input or you just
  -- accumulate saved inputs continuously.
  ( -- Compute f(x) from x
    xagGates
      -- Copy that result into fresh ancillas
      ++ fwdCopyGates
      -- Uncompute f(x), leaving the copy and our original x
      ++ reverse xagGates
      -- Swap f(x) with x, so f(x) is in the original qubits
      -- (but we still have to get rid of the input, x!)
      ++ zipWith Swapper copyNames inoutNames
      -- Compute x from f(x), using f^-1
      ++ invXAGGates
      -- Cancel out the x we previously stored, using the computed one
      ++ revCopyGates
      -- Uncompute x, leaving us with just f(x) and clean ancillas
      ++ reverse invXAGGates,
    ancillaNames'''
  )
  where
    (copyPrefix, ancillaNames') = (head ancillaNames, tail ancillaNames)
    copyNames = map (copyPrefix ++) inoutNames

    (fwdOutIDs, xagGates, ancillaNames'') = toMCTs fwdXAG inoutNames ancillaNames'
    fwdCopyGates = zipWith (\q c -> MCT [q] c) fwdOutIDs copyNames

    (revOutIDs, invXAGGates, ancillaNames''') = toMCTs revXAG inoutNames ancillaNames''
    revCopyGates = zipWith (\q c -> MCT [q] c) revOutIDs copyNames

minimizeXAG :: (HasFeynmanControl) => XAG.Graph -> XAG.Graph
minimizeXAG =
  XAG.mergeStructuralDuplicates
    . if ctlEnabled fcfFeature_Synthesis_XAG_MinMultSat
      then (\g -> fromMaybe g (XAG.resynthesizeMinMultSat g))
      else id
