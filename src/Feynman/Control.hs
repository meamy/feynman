{-# HLINT ignore "Use camelCase" #-}
module Feynman.Control where

import Data.Maybe (isJust)
import qualified Debug.Trace

-- These names are super long to avoid namespace clashes; you don't generally
-- interact with them directly so there's not as much cost to verbosity
data FeynmanControl = FeynmanControl
  { -- Log each synthesis step as it occurs
    fcfTrace_Synthesis_Pathsum_Unitary :: Bool,
    fcfTrace_Synthesis_XAG :: Bool,
    fcfTrace_Graph :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_AffineSynth :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_MCTSynth :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_XAGSynth :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_MCRzPhase :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase :: Bool,
    fcfFeature_Synthesis_Pathsum_Unitary_XAGRzPhase :: Bool,
    fcfFeature_Synthesis_XAG_Direct :: Bool,
    fcfFeature_Synthesis_XAG_Strash :: Bool,
    fcfFeature_Synthesis_XAG_MinMultSat :: Bool
  }

defaultControl :: FeynmanControl
defaultControl =
  FeynmanControl
    { fcfTrace_Synthesis_Pathsum_Unitary = False,
      fcfTrace_Synthesis_XAG = False,
      fcfTrace_Graph = False,
      fcfFeature_Synthesis_Pathsum_Unitary_AffineSynth = True,
      fcfFeature_Synthesis_Pathsum_Unitary_MCTSynth = False,
      fcfFeature_Synthesis_Pathsum_Unitary_XAGSynth = False,
      fcfFeature_Synthesis_Pathsum_Unitary_MCRzPhase = True,
      fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase = False,
      fcfFeature_Synthesis_Pathsum_Unitary_XAGRzPhase = False,
      fcfFeature_Synthesis_XAG_Direct = False,
      fcfFeature_Synthesis_XAG_Strash = False,
      fcfFeature_Synthesis_XAG_MinMultSat = False
    }

-- This is pretty meh, but when I considered giving making these switches into
-- enumerated types, I realized I'd be writing more lines of code, and then
-- the switch system itself would be nonuniform and more complicated, which
-- kind of defeats the whole purpose.

reset_fcfFeature_Synthesis_Pathsum_Unitary_Synth fc =
  fc
    { fcfFeature_Synthesis_Pathsum_Unitary_AffineSynth = False,
      fcfFeature_Synthesis_Pathsum_Unitary_MCTSynth = False,
      fcfFeature_Synthesis_Pathsum_Unitary_XAGSynth = False
    }

reset_fcfFeature_Synthesis_Pathsum_Unitary_Phase fc =
  fc
    { fcfFeature_Synthesis_Pathsum_Unitary_MCRzPhase = False,
      fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase = False,
      fcfFeature_Synthesis_Pathsum_Unitary_XAGRzPhase = False
    }

reset_fcfFeature_Synthesis_XAG fc =
  fc
    { fcfFeature_Synthesis_XAG_Direct = False,
      fcfFeature_Synthesis_XAG_Strash = False,
      fcfFeature_Synthesis_XAG_MinMultSat = False
    }

isControlSwitch :: String -> Bool
isControlSwitch s = isJust (controlSwitchFunction s)

controlSwitchFunction :: String -> Maybe (FeynmanControl -> FeynmanControl)
controlSwitchFunction "trace-unitary" = Just (\fc -> fc {fcfTrace_Synthesis_Pathsum_Unitary = True})
controlSwitchFunction "trace-xag" = Just (\fc -> fc {fcfTrace_Synthesis_XAG = True})
controlSwitchFunction "trace-graph" = Just (\fc -> fc {fcfTrace_Graph = True})
controlSwitchFunction "unitary-ket-original" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Synth fc) {fcfFeature_Synthesis_Pathsum_Unitary_AffineSynth = True})
controlSwitchFunction "unitary-ket-mct" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Synth fc) {fcfFeature_Synthesis_Pathsum_Unitary_MCTSynth = True})
controlSwitchFunction "unitary-ket-xag" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Synth fc) {fcfFeature_Synthesis_Pathsum_Unitary_XAGSynth = True})
controlSwitchFunction "unitary-phase-original" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Phase fc) {fcfFeature_Synthesis_Pathsum_Unitary_MCRzPhase = True})
controlSwitchFunction "unitary-phase-mct-rz" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Phase fc) {fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase = True})
controlSwitchFunction "unitary-phase-xag-rz" =
  Just (\fc -> (reset_fcfFeature_Synthesis_Pathsum_Unitary_Phase fc) {fcfFeature_Synthesis_Pathsum_Unitary_XAGRzPhase = True})
controlSwitchFunction "xag-direct" =
  Just (\fc -> (reset_fcfFeature_Synthesis_XAG fc) {fcfFeature_Synthesis_XAG_Direct = True})
controlSwitchFunction "xag-strash" =
  Just (\fc -> (reset_fcfFeature_Synthesis_XAG fc) {fcfFeature_Synthesis_XAG_Strash = True})
controlSwitchFunction "xag-minmultsat" =
  Just (\fc -> (reset_fcfFeature_Synthesis_XAG fc) {fcfFeature_Synthesis_XAG_MinMultSat = True})
controlSwitchFunction _ = Nothing

ctlEnabled :: (?feynmanControl :: FeynmanControl) => (FeynmanControl -> Bool) -> Bool
ctlEnabled fcf = fcf ?feynmanControl

traceIf :: Bool -> String -> a -> a
traceIf True msg x = Debug.Trace.trace msg x
traceIf False _ x = x

traceValIf :: Bool -> (a -> String) -> a -> a
traceValIf True msgF x = Debug.Trace.trace (msgF x) x
traceValIf False _ x = x
