{-# LANGUAGE TypeFamilies #-}

{-|
Module      : SArith
Description : Symbolic integer arithmetic
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.SArith where

import Data.Maybe (isJust, fromJust)
import Data.Bits
import Data.List (unfoldr, singleton)

import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Property ((==>))

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear

{---------------------------
 Core types
 ----------------------------}

-- | Symbolic (bit-blasted) unsigned integers. The lowest-order bit is the first bit
type SUInt v = [SBool v]

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
makeSUInt i n
  | i < 0     = makeSUInt ((1 `shiftL` n) - 1) n
  | otherwise = setWidth (makeSNat i) n

-- | Turns a positive integer into a symbolic uint of arbitrary length
makeSNat :: MVar v => Integer -> SUInt v
makeSNat i
  | i == 0    = []
  | i < 0     = error "Can't represent signed integers"
  | otherwise = case i `mod` 2 of
      0 -> 0:makeSNat (i `shiftR` 1)
      1 -> 1:makeSNat (i `shiftR` 1)

-- | Converts a constant bit-blasted integer back to an integer
toNat :: MVar v => SUInt v -> Maybe Integer
toNat si = case all isConstant si of
  True  -> Just . foldr (+) 0 . map f $ zip [0..] si
  False -> Nothing
  where f (i,p) = if (testFF2 $ getConstant p) then 1 `shiftL` i else 0

-- | Checks whether a symbolic uint is a constant value
isNat :: MVar v => SUInt v -> Bool
isNat = isJust . toNat

-- | Forces a symbolic uint to a Nat. Throws an error if it is symbolic
forceNat :: MVar v => SUInt v -> Integer
forceNat = fromJust . toNat

-- | given x:uint[n], generates the list of indicator polynomials:
--    [x==0, x==1, x==2, ..., x==2^n-1]
indicators :: MVar v => SUInt v -> [SBool v]
indicators = f . reverse
  where
    f [p]    = [1 + p, p]
    f (p:ps) = map ((1+p)*) (f ps) ++ map (p*) (f ps)

-- | given f, s:uint[m], t:uint[n], outputs
--    {t==0}s + {t==1}f(s) + ... + {t==i}f^i(s)[i] + ... + {t==2^n-1}(...)
--    in other words, takes the dot product of the list of indicator polynomials with the list [f^i(s)]
--    then sums over each index 
indicatorSum :: MVar v => (SUInt v -> SUInt v) -> SUInt v -> SUInt v -> SUInt v
indicatorSum f s t = foldr (zipWith (+)) (repeat 0) $ zipWith (\l ind -> map (ind*) l) (iterate f s) (indicators t)

{---------------------------
 Bitwise operators

 And, Or, Xor, Negate, LShift, RShift, LRot, RRot, Popcount
 ----------------------------}

-- | Bitwise AND
sAnd :: MVar v => SUInt v -> SUInt v -> SUInt v
sAnd s t
  | length s < length t = sAnd t s
  | otherwise           = zipWith (*) s (t ++ repeat 0)

sXor :: MVar v => SUInt v -> SUInt v -> SUInt v
sXor s t
  | length s < length t = sXor t s
  | otherwise           = zipWith (+) s (t ++ repeat 0)

-- | Bitwise NOT
sNegate :: MVar v => SUInt v -> SUInt v
sNegate = map (1+)

sOr :: MVar v => SUInt v -> SUInt v -> SUInt v
sOr s t = sNegate $ (sNegate s) `sAnd` (sNegate t)

sLShift :: MVar v => SUInt v -> SUInt v -> SUInt v
sLShift = indicatorSum lshift
  where
    lshift x = 0 : init x

sRShift :: MVar v => SUInt v -> SUInt v -> SUInt v
sRShift = indicatorSum rshift
  where
    rshift (_:x) = x ++ [0]

sLRot :: MVar v => SUInt v -> SUInt v -> SUInt v
sLRot = indicatorSum lrot
  where
    lrot x = last x : init x

sRRot :: MVar v => SUInt v -> SUInt v -> SUInt v
sRRot = indicatorSum rrot
  where
    rrot (a:x) = x ++ [a]

sPopcount :: MVar v => SUInt v -> SUInt v
sPopcount s = foldl sPlus (replicate (length s) 0) . map singleton $ s

{---------------------------
 Arithmetic operators

 Plus, Minus, Neg, Times, Div, Mod, Pow
 ----------------------------}

-- | plus(x, y)[i] = x[i] + y[i] + c[i-1]
--            c[i] = x[i] y[i] + (x[i] + y[i]) c[i-1] 
--                 = x[i] y[i] + plus(x, y)[i] c[i-1] 
--   cast to size of first arg
sPlus :: MVar v => SUInt v -> SUInt v -> SUInt v
sPlus s t = unfoldr computePair start
  where
    start                       = (0, s, t ++ repeat 0)
    computePair (_, []  , _   ) = Nothing
    computePair (c, x:xs, y:ys) = Just (c + x + y, (x * y + (x + y)*c, xs, ys))

{---------------------------
 Comparison operators

 <, <=, ==, >, >=
 ----------------------------}

{---------------------------
 Testing
 ----------------------------}

-- Convenience definition for testing
liftNat :: Integer -> SUInt String
liftNat = makeSNat

-- dropSymbolic . liftSymbolic is the identity
prop_SUInt_faithful a = (a >= 0) ==> case (toNat $ liftNat a) of
  Nothing -> False
  Just b  -> b == a

-- Plus commutes with liftSymbolic
prop_sAnd_correct a b = (a >= 0) && (b >= 0) ==>
  forceNat (sAnd (liftNat a) (liftNat b)) == a .&. b

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_SUInt_faithful
  quickCheck $ prop_sAnd_correct
