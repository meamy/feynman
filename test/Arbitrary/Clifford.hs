module Arbitrary.Clifford where

import Test.QuickCheck hiding (maxSize)

import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Core

-- | Clifford basis
xGate :: Pathsum DMod2
xGate = xgate

zGate :: Pathsum DMod2
zGate = zgate

sGate :: Pathsum DMod2
sGate = sgate

hGate :: Pathsum DMod2
hGate = hgate

cxGate :: Pathsum DMod2
cxGate = cxgate

-- | More challenging circuits
test1 = (hGate <> hGate) .> cxGate .> (hGate <> hGate)
test2 = (hGate <> identity 1) .> cxGate .> (hGate <> identity 1)
test3 = (identity 1 <> hGate) .> cxGate .> (identity 1 <> hGate)

{-----------------------------------
 Automated tests
 -----------------------------------}

-- | Maximum size of circuits
maxSize :: Int
maxSize = 9

-- | Maximum length of circuits
maxGates :: Int
maxGates = 100

-- | Type for generating instances of Clifford circuits
newtype Clifford = Clifford [Primitive] deriving (Show, Eq)

instance Arbitrary Clifford where
  arbitrary = fmap Clifford $ resize maxGates $ listOf $ oneof gates where
    gates = [genH maxSize, genS maxSize, genCX maxSize]

-- | Random CX gate
genCX :: Int -> Gen Primitive
genCX n = do
  x <- chooseInt (0, n)
  y <- chooseInt (0, n) `suchThat` (/= x)
  return $ CNOT (var x) (var y)

-- | Random S gate
genS :: Int -> Gen Primitive
genS n = do
  x <- chooseInt (0,n)
  return $ S (var x)

-- | Random H gate
genH :: Int -> Gen Primitive
genH n = do
  x <- chooseInt (0,n)
  return $ H (var x)

var :: Int -> ID
var = ("q" ++) . show

-- | Generates a random Clifford circuit
generateClifford :: Int -> Int -> IO [Primitive]
generateClifford n k = generate customArbitrary where
  customArbitrary = resize k $ listOf1 $ oneof [genH n, genS n, genCX n]

