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

data BOp = Plus | Minus | Times | Div | Mod | Pow
         | LShift | RShift | LRot | RRot
         deriving (Show)

data UOp = Neg | Wt | Exp | Sqrt deriving (Show)

-- | Classical types which can be in superposition
--
--   Register types are interpreted as unsigned integers
--   and can be dereferenced to get individual bits
--
--   The literals 0 and 1 are overloaded as both bits and
--   integers
data Type = Bit | Reg SExpr deriving Show

-- | Sum-over-path expressions
data SExpr = Var ID (Maybe SExpr)
           | VarDec ID Type
           | ILit Int
           | RLit Double
           | Pi
           | BExp SExpr BOp SExpr
           | UExp UOp SExpr
           -- Sum terms
           | Ket SExpr
           | Fun [(ID,Maybe Type)] SExpr
           | Sum [(ID,Maybe Type)] SExpr
           | Tensor SExpr SExpr
           | Compose SExpr SExpr
           | Dagger SExpr
           deriving (Show)

-- | Assertions. Conjunctions of assertions are represented as lists
data Assertion = Equals SExpr SExpr

{- Semantic checks -}

{- Parsing -}
{--

  ################### Abstract

  <expr> := <int> | <real> | <var>([<nat>])?
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
  <bop>  := + | - | * | / | ^ | % | << | >> | <<< | >>>
  <type> := bit | bit[<expr>] | uint[<expr>]

  ################### Concrete

  <type> := bit | bit[<expr>] | uint[<expr>]

  <specification> := <exprs> --> <exprs>
                   | <assertions>
 
  <assertions> := <assertion>
                | <assertions> && <assertion>

  <assertion> := <sexprs> == <sexprs>

  <sexprs> := <sexpr>
            | <sexprs> , <sexpr>

  <sexpr> := <expr>
           | fun <decls> -> <sexpr>
           | sum { <decls> } . <sexpr>

  <expr> := <term>
          | <expr> + <term>
          | <expr> - <term>
          | <expr> % <term>

  <term> := <factor>
          | <term> * <factor>
          | <term> / <factor>
          | <term> ^ <factor>

  <factor> := <appl>
            | <factor> << <appl>
            | <factor> <<< <appl>
            | <factor> >> <appl>
            | <factor> >>> <appl>

  <appl> := <atom>
          | <appl> <atom>

  <atom> := <bool>
          | <nat>
          | <real>
          | pi
          | <id>
          | <id> [ <expr> ]
          | ( expr )
          | | <exprs> >
          | < <exprs> |
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
