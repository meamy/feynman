{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}

module Feynman.Control where

import qualified Debug.Trace

-- These names are super long to avoid namespace clashes; you don't generally
-- interact with them directly so there's not as much cost to verbosity
data FeynmanControl = FeynmanControl
  { -- Log each synthesis step as it occurs
    feynmanControlTraceResynthesis :: Bool,
    feynmanControlUseMCTSynthesis :: Bool,
    feynmanControlUseNaiveXAGSynthesis :: Bool,
    feynmanControlUseBasicXAGSynthesis :: Bool,
    feynmanControlUseMinMultSatXAGSynthesis :: Bool,
    feynmanControlUseAncillaPhaseSynthesis :: Bool
  }

type HasFeynmanControl = (?feynmanControl :: FeynmanControl)

-- These are the shorthand getters you want to be using
ctlTraceResynthesis :: (HasFeynmanControl) => Bool
ctlTraceResynthesis = feynmanControlTraceResynthesis ?feynmanControl

ctlUseMCTSynthesis :: (HasFeynmanControl) => Bool
ctlUseMCTSynthesis = feynmanControlUseMCTSynthesis ?feynmanControl

ctlUseNaiveXAGSynthesis :: (HasFeynmanControl) => Bool
ctlUseNaiveXAGSynthesis = feynmanControlUseNaiveXAGSynthesis ?feynmanControl

ctlUseBasicXAGSynthesis :: (HasFeynmanControl) => Bool
ctlUseBasicXAGSynthesis = feynmanControlUseBasicXAGSynthesis ?feynmanControl

ctlUseMinMultSatXAGSynthesis :: (HasFeynmanControl) => Bool
ctlUseMinMultSatXAGSynthesis = feynmanControlUseMinMultSatXAGSynthesis ?feynmanControl

ctlUseAncillaSynthesis :: (HasFeynmanControl) => Bool
ctlUseAncillaSynthesis = ctlUseMCTSynthesis || ctlUseNaiveXAGSynthesis || ctlUseBasicXAGSynthesis || ctlUseMinMultSatXAGSynthesis

ctlUseAncillaPhaseSynthesis :: (HasFeynmanControl) => Bool
ctlUseAncillaPhaseSynthesis = feynmanControlUseAncillaPhaseSynthesis ?feynmanControl

traceResynthesis :: (HasFeynmanControl) => String -> a -> a
traceResynthesis msg x
  | ctlTraceResynthesis = Debug.Trace.trace msg x
  | otherwise = x

traceResynthesisF :: (HasFeynmanControl) => (a -> String) -> a -> a
traceResynthesisF msgF x = traceResynthesis (msgF x) x
