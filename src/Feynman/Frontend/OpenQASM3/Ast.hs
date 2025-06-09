module Feynman.Frontend.OpenQASM3.Ast (Node (..), SourceRef (..), isNilNode) where

data SourceRef where
  NilRef :: SourceRef
  TextRef :: {sourceModule :: String, sourceLine :: Int, sourceColumn :: Maybe Int} -> SourceRef
  deriving (Eq, Read, Show)

data Node t c where
  NilNode :: Node t c
  Node :: {tag :: t, children :: [Node t c], context :: c} -> Node t c
  deriving (Eq, Read, Show)

isNilNode :: Node t c -> Bool
isNilNode NilNode = True
isNilNode _ = False
