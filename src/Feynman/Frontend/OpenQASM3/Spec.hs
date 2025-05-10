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

data UOp = Neg | Wt | Exp | Sqrt deriving (Show)

-- | Classical types which can be in superposition
data Type = Bit | ZN Int deriving Show

-- | Sum-over-path expressions
data SExpr = Var ID (Maybe Int)
           | BLit Bool
           | ILit Int
           | RLit Double
           | Pi
           | BExp SExpr BOp SExpr
           | UExp Uop SExpr
           -- Sum terms
           | Ket SExpr
           | Fun ID Type SExpr
           | Sum ID Type SExpr
           | Comma SExpr SExpr
           | Compose SExpr SExpr
           | Dagger SExpr
           deriving (Show)

-- | Assertions. Conjunctions of assertions are represented as lists
data Assertion = Equals SOP SOP

{- Semantic checks -}

{- Parsing -}
{--

 Abstract

  <expr> := 0 | 1 | <nat> | <real> | <var>([<nat>])?
          | <uop> <expr>
          | <expr> <uop> <expr>
          | ( <expr> )
          | | <expr> >
          | fun <var>(:<type>)? -> <expr>
          | sum <var>(:<type>)? . <expr>
          | <expr> , <expr>
          | <expr> <expr>
          | <expr>`

  <uop>  := ! | ~ | - | popcount | exp | sqrt
  <bop>  := + | - | * | / | % | | << | >> | <<< | >>>
  <type> := bool | bit[<expr>] | uint[<expr>]

  Concrete

  <type> := bool | bit[<expr>] | uint[<expr>]

  <specification> := <exprs> --> <exprs>
                   | <assertions>
 
  <assertions> := <assertion>
                | <assertions> && <assertion>

  <assertion> := <exprs> == <exprs>

  <exprs> := <expr>
           | <exprs> , <expr>

  <expr> := <term>
          | <expr> + <term>
          | <expr> - <term>
          | <expr> % <term>

  <term> := <factor>
          | <term> * <factor>
          | <term> / <factor>

  <factor> := <atom>
            | <factor> << <atom>
            | <factor> <<< <atom>
            | <factor> >> <atom>
            | <factor> >>> <atom>

  <atom> := <bool>
          | <nat>
          | <real>
          | pi
          | <id>
          | <id> [ <expr> ]
          | ( expr )
          | | <exprs> >
          | < <exprs> |
          | fun <decls> <var>(:<type>)? -> <expr>
          | sum <decls> <var>(:<type>)? . <expr>
          | <atom>`
          | ! <atom>
          | ~ <atom>
          | - <atom>
          | <unary> ( <expr> )

  <decls> := <decl>
           | <decl> , <decls>

  <decl> := <var>
          | <var> : <type>

  <unary> := exp | popcount | sqrt

--}

{- Translation to Balanced Pathsums -}
