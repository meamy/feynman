{-# LANGUAGE DeriveGeneric #-}

module Feynman.Frontend.OpenQASM3.Ast (Node (..), SourceRef (..), isNilNode) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

data SourceRef where
  NilRef :: SourceRef
  TextRef :: {sourceModule :: String, sourceLine :: Int, sourceColumn :: Maybe Int} -> SourceRef
  deriving (Eq, Read, Show, Generic)

data Node t c where
  NilNode :: Node t c
  Node :: {tag :: t, children :: [Node t c], context :: c} -> Node t c
  deriving (Eq, Read, Show, Generic)

instance NFData SourceRef

instance forall t c. (NFData t, NFData c) => NFData (Node t c)

isNilNode :: Node t c -> Bool
isNilNode NilNode = True
isNilNode _ = False
