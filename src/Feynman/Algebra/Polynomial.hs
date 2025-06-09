{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Polynomial
Description : Polynomial base
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial(
  Degree(..),
  Vars(..),
  Ring(..),
  Field(..),
  Group(..),
  Symbolic(..)) where

import Data.Set (Set)

import Feynman.Algebra.Base

-- | Class of things that have a degree
class Degree a where
  degree :: a -> Int

-- | Class of things that have variables
class Vars a where
  type Var a
  vars :: a -> Set (Var a)

-- | Class of rings for the purpose of polynomials
class (Eq r, Num r) => Ring r

-- | Class of Fields for the purpose of polynomials
class (Ring r, Fractional r) => Field r

-- | Class of groups for the purpose of polynomials
class (Monoid m) => Group m where
  (./.) :: m -> m -> m

-- | Class of symbolic values
class Vars a => Symbolic a where
  ofVar :: Var a -> a

{- Instances -}

instance Ring FF2
instance Field FF2
