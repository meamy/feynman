{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Polynomial
Description : Polynomial base
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial(Degree(..), Vars(..)) where

import Data.Set (Set)

-- | Class of things that have a degree
class Degree a where
  degree :: a -> Int

-- | Class of things that have variables
class Vars a where
  type Var a
  vars :: a -> Set (Var a)
