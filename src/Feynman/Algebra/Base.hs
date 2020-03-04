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
  DyadicRational(..),
  DMod2,
  zero,
  one,
  dyadic,
  denom,
  dMod2,
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

instance ZModule Integer where
  power = (*)

instance ZModule Double where
  power a = (fromIntegral a *)

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
  {-# MINIMAL fromDyadic #-}
  fromDyadic :: DyadicRational -> r
  half       :: r
  divTwo     :: r -> r
  -- default implementations
  {-# INLINE half #-}
  {-# INLINE divTwo #-}
  half   = fromDyadic $ dyadic 1 1
  divTwo = (* half)

instance TwoRegular Double where
  fromDyadic (Dy a n) = (fromIntegral a) / 2^n
  half                = 0.5
  divTwo              = (* 0.5)

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

instance Fractional FF2 where
  (FF2 x) / (FF2 y) = FF2 $ x && y
  recip x           = x
  fromRational a    = (fromInteger $ numerator a) / (fromInteger $ denominator a)

{-------------------------------
 Dyadics
 -------------------------------}

-- | Dyadic rationals
data DyadicRational = Dy {-# UNPACK #-} !Integer {-# UNPACK #-} !Int deriving (Eq)

instance Show DyadicRational where
  show (Dy a 0) = show a
  show (Dy a n) = show a ++ "/2" ++ (Unicode.supscript $ toInteger n)

instance Ord DyadicRational where
  compare (Dy a n) (Dy b m)
    | n == m    = compare a b
    | otherwise = compare (a `shiftL` (n'-n)) (b `shiftL` (n'-m))
      where n' = max n m

-- | Inefficient, but exact representation
instance Real DyadicRational where
  toRational (Dy a n) = a%(1 `shiftL` n)

instance Num DyadicRational where
  (Dy a n) + (Dy b m)
    | a == 0          = Dy b m
    | b == 0          = Dy a n
    | n == m          = canonicalize $ Dy (a + b) n
    | otherwise       = canonicalize $ Dy (a `shiftL` (n'-n) + b `shiftL` (n'-m)) n'
      where n' = max n m

  (Dy a n) * (Dy b m) = canonicalize $ Dy (a * b) (n + m)
  negate (Dy a n)     = canonicalize $ Dy (-a) n
  abs (Dy a n)        = Dy a n
  signum (Dy a _n)    = Dy (signum a) 0
  fromInteger i       = Dy i 0

instance ZModule DyadicRational where
  power i (Dy a n) = canonicalize $ Dy (i*a) n

instance TwoRegular DyadicRational where
  fromDyadic      = id
  half            = Dy 1 1
  divTwo (Dy a n) = Dy a (n+1)

-- | Write in a normalized, canonical form
canonicalize :: DyadicRational -> DyadicRational
canonicalize (Dy a n)
  | a == 0                  = Dy 0 0
  | n <  0                  = Dy (a `shiftL` (-n)) 0
  | a `mod` 2 == 0 && n > 0 =
    let lg = I# (integerLog2# $ a .&. complement (a-1)) in
      if lg > n
      then Dy (a `shiftR` n) 0
      else Dy (a `shiftR` lg) (n-lg)
  | otherwise               = Dy a n

-- | Construct a canonical dyadic fraction
dyadic :: Integer -> Int -> DyadicRational
dyadic a n = canonicalize $ Dy a n

-- | Reduce a dyadic fraction mod 2
reduce :: DyadicRational -> DyadicRational
reduce (Dy a n) = Dy (a .&. ((1 `shiftL` (n+1)) - 1)) n

-- | Get the denominator of a dyadic fraction
denom :: DyadicRational -> Integer
denom (Dy _ n) = 1 `shiftL` n

-- | Dyadic fractions between 0 and 2
newtype DMod2 = D2 DyadicRational deriving (Eq, Ord)

instance Show DMod2 where
  show (D2 a) = show a

instance Real DMod2 where
  toRational (D2 a) = toRational a

instance Num DMod2 where
  (D2 a) + (D2 a') = D2 . reduce $ a + a'
  (D2 a) * (D2 a') = D2 $ a * a'
  negate (D2 a)    = D2 . reduce $ negate a
  abs (D2 a)       = D2 $ abs a
  signum (D2 a)    = D2 $ signum a
  fromInteger i    = D2 . reduce $ fromInteger i

instance ZModule DMod2 where
  power i (D2 a) = D2 . reduce $ power i a

instance Periodic DMod2 where
  order (D2 a)   = 2 * denom a

instance TwoRegular DMod2 where
  fromDyadic    = D2 . reduce
  half          = D2 half
  divTwo (D2 a) = D2 $ divTwo a

-- | Construct a dyadic fraction mod 2
dMod2 :: Integer -> Int -> DMod2
dMod2 a = D2 . reduce . dyadic a
