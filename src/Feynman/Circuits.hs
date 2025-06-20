{-|
Module      : Circuits
Description : Various circuit constructors
Copyright   : (c) 2016-2025 Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

This module contains circuits and circuit constructors
for some basic unitaries and algorithms.
-}

module Feynman.Circuits where

import Feynman.Core
import Feynman.Optimization.PhaseFold

{- ------------------------------------------------------- -}
-- * Basic circuits

-- | Controlled-S gate
cs :: ID -> ID -> [Primitive]
cs x y = [T x, T y, CNOT x y, Tinv y, CNOT x y]

-- | Controlled-Z gate
cz :: ID -> ID -> [Primitive]
cz x y = [S x, S y, CNOT x y, Sinv y, CNOT x y]

-- | Toffoli gate
ccx :: ID -> ID -> ID -> [Primitive]
ccx x y z = [H z] ++ ccz x y z ++ [H z]

-- | Doubly-controlled Z
ccz :: ID -> ID -> ID -> [Primitive]
ccz x y z = [T x, T y, T z, CNOT x y, CNOT y z,
             CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
             Tinv x, CNOT y z, CNOT z x, CNOT x y]

{- ------------------------------------------------------- -}
-- * Arithmetic circuits

-- | Controlled carry-ripple adder. 3(n-1) + 1 Toffolis
controlledAdder :: [ID] -> [ID] -> ID -> [Primitive]
controlledAdder a b ctrl =
  let anc            = ["_anc" ++ show i | i <- [0..]]
      maj2 b c t     = ccx c b t
      maj a b c t    = [CNOT c a, CNOT c b, CNOT c t] ++ ccx a b t
      go [] []  _ _  = []
      go [] [b] c _  = ccx ctrl c b
      go [a] [b] c _ = [CNOT a c] ++ ccx ctrl c b ++ [CNOT a c]
      go (a:as) (b:bs) c (t:ts) = maj a b c t ++
                                  go as bs t ts ++
                                  dagger (maj a b c t) ++
                                  [CNOT a c] ++
                                  ccx ctrl c b ++
                                  [CNOT a c]
  in
    go a b (head anc) (tail anc)

-- | Cucarro in-place adder. 2(n-1) Toffolis 
cucarro :: [ID] -> [ID] -> [Primitive]
cucarro a b =
  let carry              = "_carry"
      maj a b c          = [CNOT c b, CNOT c a] ++ ccx a b c
      uma a b c          = ccx a b c ++ [CNOT c a, CNOT a b]
      go c [a] [b,b']    = maj c b a ++ [CNOT a b'] ++ uma c b a
      go c (a:as) (b:bs) = maj c b a ++ go a as bs ++ uma c b a
  in
    go carry (reverse a) (reverse b)

{- ------------------------------------------------------- -}
-- * Algorithms

-- | Embedded, adder-based QFT. Register @x@ holds the data qubits, and @y@ the phase gradient
embeddedQFT :: Int -> [Primitive]
embeddedQFT n =
  let reg  = ["x" ++ show i | i <- [1..n]]
      cat  = reverse $ ["y" ++ show i | i <- [1..n]]
      go [x] _ = [H x]
      go (x:xs) (y:ys) = [H x] ++
                         controlledAdder (reverse xs) (y:ys) x ++
                         go xs ys
  in
    go reg cat
