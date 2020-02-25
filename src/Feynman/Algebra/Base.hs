{-# LANGUAGE MagicHash #-}

{-|
Module      : Base
Description : Various rings & other algebras
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Base(
  ZModule(..),
  Periodic(..),
  TwoRegular(..),
  FF2,
  DyadicRational,
  ProperDyadic,
  zero,
  one,
  dyadic,
  denom,
  properDyadic,
  fromDyadic,
  )
where

import Data.Bits
import Data.Ratio

import GHC.Integer.Logarithms
import GHC.Types

import qualified Feynman.Util.Unicode as Unicode

{-------------------------------
 Constants
 -------------------------------}

-- | The additive ring unit
zero :: Num a => a
zero = fromInteger 0

-- | The multiplicative ring unit
one :: Num a => a
one = fromInteger 1

{-------------------------------
 Z-modules
 -------------------------------}

-- | Groups (typically using addition in 'Num') with
--   a \(\mathbb{Z}\)-action
class Num g => ZModule g where
  power :: Integer -> g -> g

-- | Groups with computable orders. Rather than the standard
--   notion, the group 'g' need not have a finite order for
--   each element. In this case, 'order g == 0', and otherwise
--
--    @'power' ('order' x) x = 'zero'@
class Num g => Periodic g where
  order :: g -> Integer

{-------------------------------
 Two-regular rings (& multiplicative groups)
 -------------------------------}

-- | Class of rings where 2 is a regular element
class Num r => TwoRegular r where
  half   :: r
  divTwo :: r -> r
  -- default implementations
  half   = divTwo 1
  divTwo = (*half)

instance TwoRegular Double where
  half = 0.5

{-------------------------------
 Boolean field
 -------------------------------}

-- | The finite field \(\mathbb{F}_2\)
newtype FF2 = FF2 Bool deriving (Eq, Ord)

instance Show FF2 where
  show (FF2 False) = "0"
  show (FF2 True)  = "1"

instance Num FF2 where
  (FF2 x) + (FF2 y) = FF2 $ x `xor` y
  (FF2 x) * (FF2 y) = FF2 $ x && y
  negate x      = x
  abs x         = x
  signum x      = x
  fromInteger x
    | x `mod` 2 == 0 = FF2 False
    | otherwise      = FF2 True

instance ZModule FF2 where
  power i          = (fromInteger i *)

instance Periodic FF2 where
  order (FF2 False) = 1
  order (FF2 True)  = 2

{-------------------------------
 Dyadics
 -------------------------------}

-- | Dyadic rationals
newtype DyadicRational = D (Integer, Int) deriving (Eq)

instance Show DyadicRational where
  show (D (a,0)) = show a
  show (D (a,n)) = show a ++ "/2" ++ (Unicode.supscript $ toInteger n)

instance Ord DyadicRational where
  compare (D (a,n)) (D (b,m))
    | n == m    = compare a b
    | otherwise = compare (a `shiftL` (n'-n)) (b `shiftL` (n'-m))
      where n' = max n m

-- | Inefficient, but exact representation
instance Real DyadicRational where
  toRational (D (a,n)) = a%(1 `shiftL` n)

instance Num DyadicRational where
  (D (a,n)) + (D (b,m))
    | a == 0            = D (b,m)
    | b == 0            = D (a,n)
    | n == m            = canonicalize $ D (a + b, n)
    | otherwise         = canonicalize $ D (a `shiftL` (n'-n) + b `shiftL` (n'-m), n')
      where n' = max n m
  (D (a,n)) * (D (b,m)) = canonicalize $ D (a * b, n + m)
  negate (D (a,n))      = canonicalize $ D (-a,n)
  abs (D (a,n))         = D (a,n)
  signum (D (a,_n))     = D (signum a,0)
  fromInteger i         = D (i,0)

instance ZModule DyadicRational where
  power i (D (a,n)) = canonicalize $ D (i*a, n)

instance TwoRegular DyadicRational where
  half             = D (1,1)
  divTwo (D (a,n)) = D (a,n+1)

-- | Write in a normalized, canonical form
canonicalize :: DyadicRational -> DyadicRational
canonicalize (D (a,n))
  | a == 0                  = D (0,0)
  | n <  0                  = D (a `shiftL` (-n), 0)
  | a `mod` 2 == 0 && n > 0 =
    let lg = I# (integerLog2# $ a .&. complement (a-1)) in
      if lg > n
      then D (a `shiftR` n, 0)
      else D (a `shiftR` lg, n-lg)
  | otherwise               = D (a,n)

-- | Construct a canonical dyadic fraction
dyadic :: Integer -> Int -> DyadicRational
dyadic a n = canonicalize $ D (a,n)

-- | Reduce a dyadic fraction mod \(\mathbb{Z}\)
reduce :: DyadicRational -> DyadicRational
reduce (D (a,n)) = D (a .&. ((1 `shiftL` n) - 1), n)

-- | Get the denominator of a dyadic fraction
denom :: DyadicRational -> Integer
denom (D (_,n)) = 1 `shiftL` n

-- | Dyadic fractions between 0 and 1
newtype ProperDyadic = PD DyadicRational deriving (Eq, Ord)

instance Show ProperDyadic where
  show (PD a) = show a

instance Real ProperDyadic where
  toRational (PD a) = toRational a

-- | Note: ProperDyadic is not a ring
instance Num ProperDyadic where
  (PD a) + (PD a') = PD . reduce $ a + a'
  (PD a) * (PD a') = PD $ a * a'
  negate (PD a)    = PD . reduce $ negate a
  abs (PD a)       = PD $ abs a
  signum (PD a)    = PD $ signum a
  fromInteger i    = PD . reduce $ fromInteger i

instance ZModule ProperDyadic where
  power i (PD a) = PD . reduce $ power i a

instance Periodic ProperDyadic where
  order (PD a)   = denom a

instance TwoRegular ProperDyadic where
  half          = PD half
  divTwo (PD a) = PD $ divTwo a

-- | Construct a dyadic fraction mod \(\mathbb{Z}\)
properDyadic :: Integer -> Int -> ProperDyadic
properDyadic a = PD . reduce . dyadic a

-- | Convert a dyadic rational to a proper fraction
fromDyadic :: DyadicRational -> ProperDyadic
fromDyadic = PD . reduce
