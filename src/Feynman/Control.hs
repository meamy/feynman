{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}

module Feynman.Control where

-- These names are super long to avoid namespace clashes; you don't generally
-- interact with them directly so there's not as much cost to verbosity
data FeynmanControl = FeynmanControl
  { -- Log each synthesis step as it occurs
    feynmanControlTraceResynthesis :: Bool,
    feynmanControlUseAncillaSynthesis :: Bool
  }

type HasFeynmanControl = (?feynmanControl :: FeynmanControl)

-- These are the shorthand getters you want to be using
ctlTraceResynthesis :: (HasFeynmanControl) => Bool
ctlTraceResynthesis = feynmanControlTraceResynthesis ?feynmanControl

ctlUseAncillaSynthesis :: (HasFeynmanControl) => Bool
ctlUseAncillaSynthesis = feynmanControlUseAncillaSynthesis ?feynmanControl
