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
import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Core hiding (dagger)
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear
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
sso circ =
  let (gates,[main])       = break (\decl -> name decl == "main") $ decls circ
      processDecl ctx decl = Map.insert (name decl) (simulateDecl ctx decl) ctx
      ctx                  = foldl' processDecl Map.empty gates
      main'                = optimize ctx (qubits circ) (inputs circ) (body main)
  in
    circ { decls = gates ++ [main { body = main' }] }

-- | Turns a symbolic execution into an operator
operatorize :: [ID] -> Pathsum DMod2 -> Pathsum DMod2
operatorize xs = bind (reverse xs)

-- | simulates a declaration
simulateDecl :: Ctx -> Decl -> Pathsum DMod2
simulateDecl ctx (Decl _ params body) = operatorize params $ go initPS body where
  n        = length params
  
  paramMap = Map.fromList $ zip params [0..]

  initPS = ket [ofVar v | v <- params]

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
    let psStmt  = operatorize params $ go initPS stmt
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

-- | Optimizes a declaration
optimizeDecl :: Ctx -> Decl -> (Decl, Pathsum DMod2)
optimizeDecl ctx (Decl name params body) = (Decl name params body', operatorize params ps) where
  n        = length params
  
  paramMap = Map.fromList $ zip params [0..]

  initPS = ket [ofVar v | v <- params]

  (body', ps) = runState (go body) initPS

  go stmt = (\a -> modify grind >> return a) =<< case stmt of
    Gate g      -> do
      ps <- get
      let ps'  = evalState (applyPrimitive g ps) paramMap
      put ps'
      if equal ps ps' then return (Gate (Uninterp "skip" [])) else return stmt

    Seq xs      -> fmap Seq $ mapM go xs

    Call f args ->
      let embedF = \i -> paramMap!(args!!i)
          psF    = embed (ctx!f) (n - length args) embedF embedF
      in do
        ps <- get
        let ps' = ps .> psF
        put ps'
        if equal ps ps' then return (Gate (Uninterp "skip" [])) else return stmt

    Repeat i stmt ->
      let psStmt = summarizeLoop i stmt in do
        modify (\ps -> ps .> psStmt)
        return stmt

  summarizeLoop i stmt =
    let psStmt  = operatorize params $ execState (go stmt) initPS
        squares = let f x = x : f (grind $ x .> x) in f psStmt
        acc j i ps = case i <= 0 of
          True  -> ps
          False ->
            let ps' = if i `mod` 2 == 1 then ps .> squares!!j else ps in
              acc (j+1) (i `shiftR` 1) ps'
    in
      acc 0 i initPS
  

-- | Optimizes a statment
optimize :: Ctx -> [ID] -> Set ID -> Stmt -> Stmt
optimize ctx qubits inputs stmt = evalState (go stmt) initPS where
  n        = length qubits
  
  qubitMap = Map.fromList $ zip qubits [0..]

  initPS = ket [if v `elem` inputs then ofVar v else 0 | v <- qubits]

  go stmt = (\a -> modify grind >> return a) =<< case stmt of
    Gate g      -> do
      ps <- get
      let ps'  = evalState (applyPrimitive g ps) qubitMap
      put ps'
      if equal ps ps' then return (Gate (Uninterp "skip" [])) else return stmt

    Seq xs      -> fmap Seq $ mapM go xs

    Call f args ->
      let embedF = \i -> qubitMap!(args!!i)
          psF    = embed (ctx!f) (n - length args) embedF embedF
      in do
        ps <- get
        let ps' = ps .> psF
        put ps'
        if equal ps ps' then return (Gate (Uninterp "skip" [])) else return stmt

    Repeat i stmt -> go (Seq $ replicate i stmt)

-- | Tests


toffoliRem = Circuit { qubits = ["x", "y", "z"],
                       inputs = Set.fromList ["z"],
                       decls  = [tof,main] }
    where tof = Decl { name = "tof",
                       params = ["x", "y", "z",
                       body = Seq [ Gate $ H "z",
                                    Gate $ T "x", Gate $ T "y", Gate $ T "z", 
                                    Gate $ CNOT "x" "y", Gate $ CNOT "y" "z", Gate $ CNOT "z" "x",
                                    Gate $ Tinv "x", Gate $ Tinv "y", Gate $ T "z",
                                    Gate $ CNOT "y" "x",
                                    Gate $ Tinv "x",
                                    Gate $ CNOT "y" "z", Gate  $ CNOT "z" "x", Gate $ CNOT "x" "y",
                                    Gate $ H "z" ] }
          main = Decl { name = "main",
                        params = [],
                        body = Seq [ Call "tof" ["x", "y", "z"] ] }
