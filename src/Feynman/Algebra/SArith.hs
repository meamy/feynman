{-# Language MultiParamTypeClasses #-}
{-# Language FunctionalDependencies #-}

{-|
Module      : SArith
Description : Symbolic integer arithmetic
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.SArith where

import Data.Maybe (isJust, fromJust)
import Data.Bits

import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Property ((==>))

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear

{---------------------------
 Core types
 ----------------------------}

-- | Symbolic (bit-blasted) unsigned integers. The lowest-order bit is the first bit
type SUInt v = [SBool v]

-- | Type class for symbolic values
class Symbolic a sa | sa -> a where
  liftSymbolic :: a -> sa
  dropSymbolic :: sa -> Maybe a

-- | Check whether a symbolic value is symbolic or not
isSymbolic :: Symbolic a sa => sa -> Bool
isSymbolic = isJust . dropSymbolic

-- | Forces a symbolic value to a constant. Throws an error if it is symbolic
forceDrop :: Symbolic a sa => sa -> a
forceDrop = fromJust . dropSymbolic

instance MVar v => Symbolic FF2 (SBool v) where
  liftSymbolic = constant
  dropSymbolic sb = case isConst sb of
    True  -> Just $ getConstant sb
    False -> Nothing

instance MVar v => Symbolic Integer (SUInt v) where
  liftSymbolic 0 = []
  liftSymbolic i
    | i < 0 = error "Can't represent signed integers"
    | otherwise = case i `mod` 2 of
        0 -> 0:liftSymbolic (i `shiftR` 1)
        1 -> 1:liftSymbolic (i `shiftR` 1)
    
  dropSymbolic si = case all isConst si of
    True  -> Just . foldr (+) 0 . map f $ zip [0..] si
    False -> Nothing
    where f (i,p) = if (testFF2 $ getConstant p) then 1 `shiftL` i else 0

{---------------------------
 Utilities
 ----------------------------}

-- | Returns the width of an SUInt
getWidth :: SUInt v -> Int
getWidth = length

-- | Truncates or extends a symbolic uint to /n/ bits
setWidth :: MVar v => SUInt v -> Int -> SUInt v
setWidth sa n = take n sa ++ (replicate (n - length sa) 0)

-- | Turns an integer into a symbolic uint[n]
makeSUInt :: MVar v => Integer -> Int -> SUInt v
makeSUInt a n
  | a < 0     = makeSUInt ((1 `shiftL` n) - 1)
  | otherwise = setWidth (liftSymbolic a) n

{---------------------------
 Bitwise operators

 And, Or, Xor, Negate, LShift, RShift, LRot, RRot, Popcount
 ----------------------------}

-- | Bitwise AND
sAnd :: MVar v => SUInt v -> SUInt v -> SUInt v
sAnd s t
  | length s < length t = sAnd t s
  | otherwise           = zipWith (*) s (t ++ repeat 0)

{---------------------------
 Arithmetic operators

 Plus, Minus, Neg, Times, Div, Mod, Pow
 ----------------------------}

{---------------------------
 Comparison operators

 <, <=, ==, >, >=
 ----------------------------}

{---------------------------
 Testing
 ----------------------------}

-- Convenience definition for testing
liftSUInt :: Integer -> SUInt String
liftSUInt = liftSymbolic

-- dropSymbolic . liftSymbolic is the identity
prop_SUInt_faithful a = (a >= 0) ==> case (dropSymbolic $ liftSUInt a) of
  Nothing -> False
  Just b  -> b == a

-- Plus commutes with liftSymbolic
prop_sAnd_correct a b = (a >= 0) && (b >= 0) ==>
  forceDrop (sAnd (liftSUInt a) (liftSUInt b)) == a .&. b

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_SUInt_faithful
  quickCheck $ prop_sAnd_correct
