{-# LANGUAGE AllowAmbiguousTypes #-}

module Feynman.Frontend where

import Feynman.Core (ID, Primitive)

import Data.ByteString
import Text.Parsec


{- Basic frontend class for optimization & verification -}
class Show a => Frontend a where
  parseIt       :: ByteString -> Either ParseError a
  commentPrefix :: String
  parameters    :: a -> [ID]
  sequentialize :: a -> [Primitive]
  optimize      :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> a -> a
  -- Optional standard operations
  statistics    :: a -> [String]
  inline        :: a -> a
  decomposeMCT  :: a -> a
  decomposeAll  :: a -> a
  simplify      :: a -> a
  -- Default instances
  statistics _ = []
  inline       = id
  decomposeMCT = id
  decomposeAll = id
  simplify     = id
