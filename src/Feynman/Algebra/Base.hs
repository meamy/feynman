module Feynman.Algebra.Base (Abelian(..),
                             Periodic(..),
                             Ring(..),
                             Field(..),
                             Dyadic(),
                             dyadic,
                             DyadicUnit(),
                             dyadicUnit)
                             where

import Data.Ratio ((%))
import Data.Bits

import Test.QuickCheck hiding ((.&.))

{- Type classes -}
{- For now, we'll just have numeric type classes specialize Num -}
class Num a => Abelian a where
  zero   :: a
  pow    :: Integer -> a -> a

class Abelian a => Periodic a where
  order :: a -> Integer

class Abelian a => Ring a where
  one :: a

class (Ring a, Fractional a) => Field a

{- Dyadic rationals -}

-- Note: Must be in the form of an odd numerator for any non-zero
-- power of 2 denominator
newtype Dyadic = Dy (Int, Word) deriving (Eq)

instance Show Dyadic where
  show (Dy (a,n)) = show a ++ "/2^" ++ show n

instance Ord Dyadic where
  compare a b = compare (toRational a) (toRational b)

instance Real Dyadic where
  toRational (Dy (a,n)) = (toInteger a)%(bit $ fromIntegral n)

instance Num Dyadic where
  (Dy (a,n)) + (Dy (b,m))
    | a == 0           = Dy (b,m)
    | b == 0           = Dy (a,n)
    | n == 0 && m == 0 = Dy (a+b, 0)
    | n == m           = reduce $ Dy (a+b, n)
    | otherwise        = Dy (a*(bit . fromIntegral $ n'-n) + b*(bit . fromIntegral $ n'-m), n')
    where n' = max n m
  (Dy (a,n)) * (Dy (b,m))
    | n == 0 || m == 0 = reduce $ Dy (a*b, n+m)
    | otherwise        = Dy (a*b, n+m)
  negate (Dy (a,n))       = Dy (negate a,n)
  abs (Dy (a,n))          = Dy (abs a,n)
  signum (Dy (a,n))       = Dy (signum a, 0)
  fromInteger i           = Dy (fromInteger i,0)

instance Abelian Dyadic where
  zero             = Dy (0,0)
  pow i (Dy (a,n)) = reduce $ Dy ((fromInteger i)*a,n)

instance Ring Dyadic where
  one  = Dy (1,0)

reduce :: Dyadic -> Dyadic
reduce (Dy (a,n))
  | n == 0    = Dy (a,n)
  | a == 0    = Dy (0,0)
  | otherwise        =
    let n' = min n (fromIntegral $ countTrailingZeros a) in
      Dy (a `shiftR` (fromIntegral n'), n-n')

dyadic :: Integral a => a -> a -> Dyadic
dyadic a n = reduce $ Dy (fromIntegral a, fromIntegral n)

{- Dyadic rationals in the unit interval -}

newtype DyadicUnit = DyadicUnit { rep :: Dyadic } deriving (Eq, Ord)

instance Show DyadicUnit where
  show a = show $ rep a

instance Real DyadicUnit where
  toRational a = toRational $ rep a

instance Num DyadicUnit where
  a + b         = normalize $ rep a + rep b
  a * b         = normalize $ rep a * rep b
  negate a      = normalize $ negate (rep a)
  abs a         = normalize $ abs (rep a)
  signum a      = normalize $ signum (rep a)
  fromInteger i = normalize $ fromInteger i

instance Abelian DyadicUnit where
  zero    = DyadicUnit (Dy (0,0))
  pow i a = normalize $ pow i (rep a)

instance Periodic DyadicUnit where
  order a = bit $ fromIntegral n
    where Dy (_,n) = rep a

normalize :: Dyadic -> DyadicUnit
normalize (Dy (a,n)) = DyadicUnit (Dy (a .&. (bit (fromIntegral n) - 1), n))

dyadicUnit :: Integral a => a -> a -> DyadicUnit
dyadicUnit a b = normalize $ dyadic a b

{- Tests -}

instance Arbitrary Dyadic where
  arbitrary = do
    a <- (arbitrary :: Gen Int)
    n <- choose (0,32)
    return $ dyadic a n

instance Arbitrary DyadicUnit where
  arbitrary = do
    a <- (arbitrary :: Gen Int)
    n <- choose (0,32)
    return $ dyadicUnit a n

reduced :: Dyadic -> Bool
reduced (Dy (a,n))
  | n == 0         = True
  | n < 0          = False
  | a `mod` 2 == 1 = True
  | otherwise      = False

unital  :: DyadicUnit -> Bool
unital d = zero <= d' && d' < one
  where d' = rep d

prop_dyadicReduced = reduced
prop_plusReduced   = reduced . uncurry (+)
prop_multReduced   = reduced . uncurry (*)
prop_negateReduced = reduced . negate
prop_powReduced    = reduced . uncurry pow

prop_dyadicUnital = unital
prop_plusUnital   = unital . uncurry (+)
prop_multUnital   = unital . uncurry (*)
prop_negateUnital = unital . negate
prop_powUnital    = unital . uncurry pow

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_dyadicReduced
  quickCheck $ prop_plusReduced
  quickCheck $ prop_multReduced
  quickCheck $ prop_negateReduced
  quickCheck $ prop_powReduced
  quickCheck $ prop_dyadicUnital
  quickCheck $ prop_plusUnital
  quickCheck $ prop_multUnital
  quickCheck $ prop_negateUnital
  quickCheck $ prop_powUnital
  
