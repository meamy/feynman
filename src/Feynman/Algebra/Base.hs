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
  Abelian(..),
  Ring(..),
  TwoRegular(..),
  Z2,
  DyadicRational,
  ProperDyadic,
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
 Groups & Rings
 -------------------------------}

-- | The Abelian group (g, +). By convention, 'order g == 0' if 'g' has
--   infinite order. Otherwise, subject to the law
--
--    @'power' ('order' x) x = 'zero'@
class Num g => Abelian g where
  zero  :: g
  power :: Integer -> g -> g
  order :: g -> Integer

-- | Rings
class Abelian a => Ring a where
  one :: a

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
newtype Z2 = Z2 Bool deriving (Eq, Ord)

instance Show Z2 where
  show (Z2 False) = "0"
  show (Z2 True)  = "1"

instance Num Z2 where
  (Z2 x) + (Z2 y) = Z2 $ x `xor` y
  (Z2 x) * (Z2 y) = Z2 $ x && y
  negate x      = x
  abs x         = x
  signum x      = x
  fromInteger x
    | x `mod` 2 == 0 = Z2 False
    | otherwise      = Z2 True

instance Abelian Z2 where
  zero             = Z2 False
  power i          = (fromInteger i *)
  order (Z2 False) = 1
  order (Z2 True)  = 2

instance Ring Z2 where
  one = Z2 True

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

instance Abelian DyadicRational where
  zero              = D (0,0)
  power i (D (a,n)) = canonicalize $ D (i*a, n)
  order _           = 0

instance Ring DyadicRational where
  one = D (1,0)

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

instance Abelian ProperDyadic where
  zero           = PD zero
  power i (PD a) = PD . reduce $ power i a
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
