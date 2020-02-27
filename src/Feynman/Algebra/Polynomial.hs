{-|
Module      : Polynomial
Description : Polynomial base
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial(Degree(..)) where

-- | Class of things that have a degree
class Degree a where
  degree :: a -> Int
