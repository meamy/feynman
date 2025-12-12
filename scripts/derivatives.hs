{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module      : Main
Description : Derivative tests
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced

import Test.QuickCheck

instance Arbitrary (SBool Var) where
  arbitrary = sized $ \n -> do
    let genMon = resize n $ listOf (elements [IVar i | i <- [0..n-1]])
    terms <- resize (2^n) $ listOf genMon
    return $ ofTermList [(1, monomial xs) | xs <- terms]

instance Arbitrary (PseudoBoolean Var DMod2) where
  arbitrary = sized $ \n -> do
    let genMon = resize n $ listOf (elements [IVar i | i <- [0..n-1]])
    let genTerm = do
          m <- genMon
          a <- chooseInt (0,7)
          return (dMod2 (toInteger a) 2, m)
    terms <- resize (2^n) $ listOf genTerm
    return $ ofTermList [(a, monomial xs) | (a,xs) <- terms]

-- | Random phase polynomial on a specific number of bits
randomBool :: Int -> Gen (SBool Var)
randomBool n = resize n arbitrary

-- | Random phase polynomial on a specific number of bits
randomPP :: Int -> Gen (PseudoBoolean Var DMod2)
randomPP n = resize n arbitrary

-- | Generates a path sum from a phase polynomial
phaseOracle :: Int -> SBool Var -> Pathsum DMod2
phaseOracle n f = Pathsum 0 n n 0 (lift f) [ofVar (IVar i) | i <- [0..n-1]]

-- | Generates a path sum from a phase polynomial
diag :: Int -> PseudoBoolean Var DMod2 -> Pathsum DMod2
diag n f = Pathsum 0 n n 0 f [ofVar (IVar i) | i <- [0..n-1]]
  
-- | Teleportation
teleN :: Int -> Pathsum DMod2
teleN n = (inp <> inp) .> cxLayer .> measureLayer .> traceLayer where
  inp          = mconcat (replicate n (fresh .> hgate)) <> identity n
  cxLayer      = compose [applyCX i (i+n) . applyCX (i + 2*n) (i + 3*n) | i <- [0..n-1]] $ identity (4*n)
  measureLayer = compose [applyCX (i+n) i . applyCX (i+3*n) (i + 2*n) . applyMeasure (i+n) (i+3*n) | i <- [0..n-1]] $ identity (4*n)
  traceLayer   = compose [traceOut (n) (3*n-i) | i <- [0..n-1]] $ identity (4*n)
  compose      = foldl (flip (.)) id

-- | Magic state injection
injectBool :: Int -> SBool Var -> Pathsum DMod2
injectBool n f = (grind $ (inp <> inp) .> phase .> cxLayer .> measureLayer) .> traceLayer where
  derivs       = [differentiate (Set.singleton (IVar i)) f | i <- [0..n-1]]
  inp          = mconcat (replicate n (fresh .> hgate)) <> identity n
  phase        = phaseOracle n f <> identity n <> dagger (phaseOracle n f) <> identity n
  cxLayer      = compose [applyCX i (i+n) . applyCX (i + 2*n) (i + 3*n) | i <- [0..n-1]] $ identity (4*n)
  measureLayer = compose [applyCorr i . grind . applyMeasure (i+n) (i+3*n) | i <- [0..n-1]] $ identity (4*n)
  traceLayer   = compose [traceOut (n) (3*n-i) | i <- [0..n-1]] $ identity (4*n)
  compose      = foldl (flip (.)) id
  applyCorr i  = compose [applyControlled (phaseOracle n (-(derivs!!i))) (i + 3*n) [2*n..3*n - 1] .
                          applyControlled (phaseOracle n (derivs!!i)) (i+n) [0..n-1] .
                          applyCX (i + 3*n) (i + 2*n) .
                          applyCX (i+n) i]

-- | Magic state injection
injectPP :: Int -> PseudoBoolean Var DMod2 -> Pathsum DMod2
injectPP n f = (grind $ (inp <> inp) .> phase .> cxLayer .> measureLayer) .> traceLayer where
  derivs       = [differentiate (Set.singleton (IVar i)) f | i <- [0..n-1]]
  inp          = mconcat (replicate n (fresh .> hgate)) <> identity n
  phase        = diag n f <> identity n <> diag n (-f) <> identity n
  cxLayer      = compose [applyCX i (i+n) . applyCX (i + 2*n) (i + 3*n) | i <- [0..n-1]] $ identity (4*n)
  measureLayer = compose [applyCorr i . grind . applyMeasure (i+n) (i+3*n) | i <- [0..n-1]] $ identity (4*n)
  traceLayer   = compose [traceOut (n) (3*n-i) | i <- [0..n-1]] $ identity (4*n)
  compose      = foldl (flip (.)) id
  applyCorr i  = compose [
                          applyCX (i + 3*n) (i + 2*n) .
                          applyCX (i+n) i .
                          applyControlled (diag n (-(derivs!!i))) (i + 3*n) [2*n..3*n - 1] .
                          applyControlled (diag n (derivs!!i)) (i+n) [0..n-1]
                         ]

-- | Teleportation in a shifted basis of stabilizers
teleNAlt :: Int -> Pathsum DMod2
teleNAlt n = (inp <> inp) .> cxLayer .> measureLayer .> traceLayer where
  inp          = mconcat (replicate n (fresh .> hgate)) <> identity n
  cxLayer      = compose [applyCX i (i+n) . applyCX (i + 2*n) (i + 3*n) | i <- [0..n-1]] $ identity (4*n)
  measureLayer = compose [cxes i . applyMeasure (i+n) (i+3*n) | i <- [0..n-1]] $ identity (4*n) where
    cxes i = case i > 1 of
      False -> applyCX (i+n) (i+1) . applyCX (i+3*n) (i+2*n + 1) . applyCX (i+n) (i+n+1) . applyCX (i+3*n) (i+3*n+1) . applyCX (i+n) i . applyCX (i+3*n) (i + 2*n)
      True -> applyCX (i+n) i . applyCX (i+3*n) (i + 2*n)
  traceLayer   = compose [traceOut (n) (3*n-i) | i <- [0..n-1]] $ identity (4*n)
  compose      = foldl (flip (.)) id

-- | Magic state injection
injectPPAlt :: Int -> PseudoBoolean Var DMod2 -> Pathsum DMod2
injectPPAlt n f = (grind $ (inp <> inp) .> phase .> cxLayer .> measureLayer) .> traceLayer where
  derivs       = [differentiate (Set.fromList [IVar i, IVar (i+1)]) f | i <- [0..1]] ++ [differentiate (Set.fromList [IVar i]) f | i <- [2..n-1]]
  inp          = mconcat (replicate n (fresh .> hgate)) <> identity n
  phase        = diag n f <> identity n <> diag n (-f) <> identity n
  cxLayer      = compose [applyCX i (i+n) . applyCX (i + 2*n) (i + 3*n) | i <- [0..n-1]] $ identity (4*n)
  measureLayer = compose [applyCorr i . grind . applyMeasure (i+n) (i+3*n) | i <- [0..n-1]] $ identity (4*n)
  traceLayer   = compose [traceOut (n) (3*n-i) | i <- [0..n-1]] $ identity (4*n)
  compose      = foldl (flip (.)) id
  applyCorr i  = case i > 1 of
    True -> compose [applyCX (i + 3*n) (i + 2*n) .
                      applyCX (i+n) i .
                      applyControlled (diag n (-(derivs!!i))) (i + 3*n) [2*n..3*n - 1] .
                      applyControlled (diag n (derivs!!i)) (i+n) [0..n-1]
                     ]
    False -> compose [applyCX (i+n) (i+1) .
                     applyCX (i + 3*n) (i + 2*n + 1) .
                     applyCX (i+n) (i+n+1) .
                     applyCX (i + 3*n) (i + 3*n + 1) .
                     applyCX (i + 3*n) (i + 2*n) .
                     applyCX (i+n) i .
                     applyControlled (diag n (-(derivs!!i))) (i + 3*n) [2*n..3*n - 1] .
                     applyControlled (diag n (derivs!!i)) (i+n) [0..n-1]
                    ]

-- | Quickcheck property
verify :: Int -> PseudoBoolean Var DMod2 -> Bool
verify n f = grind (teleN n .> (diag n f <> diag n (-f))) == grind (injectPP n f)

-- | Quickcheck property
verifyAlt :: Int -> PseudoBoolean Var DMod2 -> Bool
verifyAlt n f = grind (teleN n .> (diag n f <> diag n (-f))) == grind (injectPPAlt n f)

-- | Main script
main :: IO ()
main = do
  putStrLn "Hello, beep boop, checker beep boop..."
  putStrLn "Checking elementary basis for 3 bits..."
  quickCheck (withMaxSize 3 $ verify 3)
  putStrLn "Checking alternate basis for 3 bits..."
  quickCheck (withMaxSize 3 $ verifyAlt 3)
  putStrLn "Checking elementary basis for 4 bits..."
  quickCheck (withMaxSize 4 $ verify 4)
  putStrLn "Checking alternate basis for 4 bits..."
  quickCheck (withMaxSize 4 $ verifyAlt 4)
