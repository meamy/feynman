{-|
Module      : Spec
Description : Specifications for openQASM 3
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.Spec where

import Feynman.Core (ID)
import Feynman.Algebra.Base (Dyadic(..), DyadicRational, DMod2)

{- Term-level syntax for path sums -}

type Angle = DMod2

data BOp = Plus | Minus | Times | Div | Mod
         | And | Xor | Or | LShift | RShift | LRot | RRot
         deriving (Show)

data UOp = Neg | Wt deriving (Show)

-- | Classical types which can be in superposition
data Type = Bit | ZN Int deriving Show

-- | Classical sub-language
data CExp = CVar ID
          | TT
          | FF
          | ILit Int
          | BExp CExp BOp CExp
          | UExp UOp CExp
          deriving (Show)

-- | Scalar sub-language. Only phases can depend on path indices
data RExp = CondPhase Angle CExp
          | Norm DyadicRational
          | Mult RExp RExp
          deriving (Show)

-- | Matrix-valued terms
data SOP = Segment [ID]
         | Ket CExp
         | Scalar RExp
         | Fun ID Type SOP
         | Sum ID Type SOP
         | Tensor SOP SOP
         | Compose SOP SOP
         | Dagger SOP
         deriving (Show)

-- | Assertions. Conjunctions of assertions are represented as lists
data Assertion = Equals SOP SOP

{- Semantic checks -}

{- Parsing -}

{- Translation to Balanced Pathsums -}
