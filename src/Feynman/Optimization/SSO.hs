{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : SSO
Description : Symbolic state optimization
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

-}

module Feynman.Optimization.SSO where

import Control.Monad
import Control.Monad.State.Strict

import Data.Bits
import Data.Foldable
import Data.Map (Map, (!))
import qualified Data.Map as Map

import Feynman.Core hiding (dagger)
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Verification.Symbolic

{-----------------------------------
 Assertion-based optimization

 The basic idea is to extract precise
 actions for composite gates at a
 hierarchical level and use this
 together with symbolic simulation
 to determine when gates act trivially
 on the state
 -----------------------------------}

-- | Summaries of previously 
type Ctx = Map ID (Pathsum DMod2)

-- | Top-level optimization
sso :: Circuit -> Circuit
sso circ = circ { decls = decls' } where
  decls' = decls circ

-- | simulates a declaration
simulateDecl :: Ctx -> Decl -> Pathsum DMod2
simulateDecl ctx (Decl _ params body) = go initPS body where
  n        = length params
  
  paramMap = Map.fromList $ zip params [0..]

  initPS = identity (length params)

  go ps stmt = grind $ case stmt of
    Gate g      -> evalState (applyPrimitive g ps) paramMap
    Seq xs      -> foldl' go ps xs
    Call f args ->
      let embedF = \i -> paramMap!(args!!i)
          psF    = embed (ctx!f) (n - length args) embedF embedF
      in
        ps .> psF
    Repeat i stmt ->
      let psStmt = summarizeLoop i stmt in
        ps .> psStmt

  summarizeLoop i stmt =
    let psStmt  = go initPS stmt
        squares = let f x = x : f (grind $ x .> x) in f psStmt
        acc j i ps = case i <= 0 of
          True  -> ps
          False ->
            let ps' = if i `mod` 2 == 1 then ps .> squares!!j else ps in
              acc (j+1) (i `shiftR` 1) ps'
    in
      acc 0 i initPS
  
-- | Checks whether the miter of two path sums is the identity
equal :: Pathsum DMod2 -> Pathsum DMod2 -> Bool
equal ps ps' = isTrivial (grind $ ps .> dagger ps')
