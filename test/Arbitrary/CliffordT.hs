module Arbitrary.CliffordT where

import Test.QuickCheck hiding (maxSize)

import Feynman.Core

-- | Maximum size of circuits
maxSize :: Int
maxSize = 9

-- | Maximum length of circuits
maxGates :: Int
maxGates = 100

-- | Type for generating instances of Clifford+T circuits
newtype CliffordT = CliffordT [Primitive] deriving (Show, Eq)

instance Arbitrary CliffordT where
  arbitrary = fmap CliffordT $ resize maxGates $ listOf $ oneof gates where
    gates = [genH maxSize, genT maxSize, genCX maxSize]

-- | Variable names
var :: Int -> ID
var i = "q" ++ show i

-- | Random CX gate
genCX :: Int -> Gen Primitive
genCX n = do
  x <- chooseInt (0,n)
  y <- chooseInt (0,n) `suchThat` (/= x)
  return $ CNOT (var x) (var y)

-- | Random S gate
genT :: Int -> Gen Primitive
genT n = do
  x <- chooseInt (0,n)
  return $ T (var x)

-- | Random H gate
genH :: Int -> Gen Primitive
genH n = do
  x <- chooseInt (0,n)
  return $ H (var x)

-- | Generates a random Clifford+T circuit
generateCliffordT :: Int -> Int -> IO [Primitive]
generateCliffordT n k = generate customArbitrary where
  customArbitrary = resize k $ listOf1 $ oneof [genH n, genT n, genCX n]

