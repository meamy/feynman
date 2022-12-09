{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  Periodic(..),
  Dyadic(..),
  Euclidean(..),
  FF2,
  Zmod,
  Z4,
  Z8,
  DyadicRational(..),
  DMod2,
  zero,
  one,
  dyadic,
  toDyadic,
  numer,
  denom,
  dMod2,
  unpack,
  )
where

import Data.Bits
import Data.Ratio
import Data.Proxy

import GHC.Integer.Logarithms
import GHC.Types
import GHC.TypeLits

import Test.QuickCheck hiding ((.&.))

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
class Num g => Abelian g where
  power :: Integer -> g -> g

instance Abelian Integer where
  power = (*)

instance Abelian Double where
  power a = (fromIntegral a *)

-- | Groups with computable orders. Rather than the standard
--   notion, the group 'g' need not have a finite order for
--   each element. In this case, 'order g == 0', and otherwise
--
--    @'power' ('order' x) x = 'zero'@
class Abelian g => Periodic g where
  order :: g -> Integer

{-------------------------------
 Two-regular rings (& multiplicative groups)
 -------------------------------}

-- | Class of rings where 2 is a regular element
class Num r => Dyadic r where
  {-# MINIMAL fromDyadic #-}
  fromDyadic :: DyadicRational -> r
  half       :: r
  divTwo     :: r -> r
  -- default implementations
  {-# INLINE half #-}
  {-# INLINE divTwo #-}
  half   = fromDyadic $ dyadic 1 1
  divTwo = (* half)

instance Dyadic Double where
  fromDyadic (Dy a n) = (fromIntegral a) / 2^n
  half                = 0.5
  divTwo              = (* 0.5)

{-------------------------------
 Euclidean domains
 -------------------------------}

-- | Euclidean domains
class Num r => Euclidean r where
  rank   :: r -> Integer
  divmod :: r -> r -> (r, r)

-- | Euclidean algorithm
euclid :: (Eq r, Euclidean r) => r -> r -> r
euclid a 0 = a
euclid a b = euclid b (snd $ divmod a b)

-- | Least common multiple in a Euclidean domain
lc :: (Eq r, Euclidean r) => r -> r -> r
lc a b = fst $ divmod (abs (a * b)) (euclid a b)

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

instance Abelian FF2 where
  power i          = (fromInteger i *)

instance Periodic FF2 where
  order (FF2 False) = 1
  order (FF2 True)  = 2

instance Fractional FF2 where
  (FF2 x) / (FF2 y) = FF2 $ x && y
  recip x           = x
  fromRational a    = (fromInteger $ numerator a) / (fromInteger $ denominator a)

instance Euclidean FF2 where
  rank _ = 1
  divmod a b = (a / b, 0)

{-------------------------------
 Finite groups
 -------------------------------}

-- | The ring of integers modulo n \(\mathbb{Z}_n\)
data Zmod (n :: Nat) where
  Zmod :: (KnownNat n) => Int -> Zmod n

instance Show (Zmod n) where
  show (Zmod i) = show i

instance forall n. (KnownNat n) => Num (Zmod n) where
  (Zmod x) + (Zmod y) = Zmod $ (x + y) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  (Zmod x) * (Zmod y) = Zmod $ (x * y) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  negate (Zmod x)     = Zmod $ (-x) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  abs x               = x
  signum x            = x
  fromInteger x       = Zmod $ (fromInteger x) `mod` (fromInteger $ natVal (Proxy::Proxy n))

instance (KnownNat n) => Abelian (Zmod n) where
  power i (Zmod x)    = Zmod $ (fromInteger i) * x `mod` (fromInteger $ natVal (Proxy::Proxy n))

instance (KnownNat n) => Periodic (Zmod n) where
  order (Zmod x) = toInteger $ (lcm x (fromInteger $ natVal (Proxy::Proxy n))) `div` x

-- | Convenience types
type Z4 = Zmod 4
type Z8 = Zmod 8

-- | Inject a modular number into \(\mathbb{Z}\)
injectMod :: Zmod n -> Integer
injectMod (Zmod x) = toInteger x

{-------------------------------
 Dyadics
 -------------------------------}

-- | Dyadic rationals
data DyadicRational = Dy !Integer {-# UNPACK #-} !Int deriving (Eq)

instance Show DyadicRational where
  show (Dy a 0) = show a
  show (Dy a n)
    | n > 0 = show a ++ "/2" ++ (Unicode.supscript $ toInteger n)
    | n < 0 = show a ++ "*2" ++ (Unicode.supscript $ toInteger (-n))

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

instance Abelian DyadicRational where
  power i (Dy a n) = canonicalize $ Dy (i*a) n

instance Dyadic DyadicRational where
  fromDyadic      = id
  half            = Dy 1 1
  divTwo (Dy a n) = Dy a (n+1)

instance Euclidean DyadicRational where
  rank (Dy a _)            = abs a
  divmod 0 _               = (0, 0)
  divmod _ 0               = (0, 0)
  divmod (Dy a n) (Dy b m) = (dyadic q (n - m), dyadic r n) where
    (q, r) = divMod a b

-- | Write in a normalized, canonical form
canonicalize :: DyadicRational -> DyadicRational
canonicalize (Dy a n)
  | a == 0                  = Dy 0 0
  | a `mod` 2 == 0 =
    let lg = I# (integerLog2# $ a .&. complement (a-1)) in
      Dy (a `shiftR` lg) (n-lg)
  | otherwise               = Dy a n

-- | Construct a canonical dyadic fraction
dyadic :: Integer -> Int -> DyadicRational
dyadic a n = canonicalize $ Dy a n

-- | Reduce a dyadic fraction mod 2
reduce :: DyadicRational -> DyadicRational
reduce (Dy a n) = Dy (a .&. ((1 `shiftL` (n+1)) - 1)) n

-- | Get the denominator of a dyadic fraction
numer :: DyadicRational -> Integer
numer (Dy a _) = a

-- | Get the denominator of a dyadic fraction
denom :: DyadicRational -> Integer
denom (Dy _ n) = 1 `shiftL` n

-- | Give the exact representation of a float as a dyadic rational
toDyadic :: RealFloat a => a -> DyadicRational
toDyadic x = dyadic a n
  where a = numerator ratRepr
        n = I# (integerLog2# $ denominator ratRepr)
        ratRepr = toRational x

-- | Dyadic fractions between 0 and 2
newtype DMod2 = D2 { unpack :: DyadicRational } deriving (Eq, Ord)

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

instance Abelian DMod2 where
  power i (D2 a) = D2 . reduce $ power i a

instance Periodic DMod2 where
  order (D2 a)   = 2 * denom a

instance Dyadic DMod2 where
  fromDyadic    = D2 . reduce
  half          = D2 half
  divTwo (D2 a) = D2 $ divTwo a

instance Euclidean DMod2 where
  rank (D2 a) = rank a
  divmod 0 _  = (0, 0)
  divmod _ 0  = (0, 0)
  divmod (D2 a) (D2 b) = (fromDyadic x, fromDyadic y) where
    (x, y) = divmod a b

-- | Construct a dyadic fraction mod 2
dMod2 :: Integer -> Int -> DMod2
dMod2 a = D2 . reduce . dyadic a

{----------------------------
 Testing
 ----------------------------}

instance Arbitrary DyadicRational where
  arbitrary = do
    a <- arbitrary `suchThat` (/= 0)
    n <- arbitrary
    return $ dyadic a n

prop_euclidean_division_rank :: DyadicRational -> DyadicRational -> Bool
prop_euclidean_division_rank a b = (rank b) > (rank $ snd (divmod a b))

prop_euclidean_division_correct :: DyadicRational -> DyadicRational -> Bool
prop_euclidean_division_correct a b = a == q*b + r where
  (q, r) = divmod a b

instance Arbitrary DMod2 where
  arbitrary = do
    a <- arbitrary `suchThat` (/= 0)
    n <- arbitrary
    return $ dMod2 a n

prop_euclidean_division_rank_dmod2 :: DMod2 -> DMod2 -> Bool
prop_euclidean_division_rank_dmod2 a b = (rank b) > (rank $ snd (divmod a b))

prop_euclidean_division_correct_dmod2 :: DMod2 -> DMod2 -> Bool
prop_euclidean_division_correct_dmod2 a b = a == q*b + r where
  (q, r) = divmod a b
