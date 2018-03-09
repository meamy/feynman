module Feynman.Algebra.Base where

import Data.Ratio

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

{- Circle groups -}

newtype Dyadic = Dy (Int, Int) deriving (Eq) -- NOTE: must be in lowest form

instance Show Dyadic where
  show (Dy (a,n)) = show a ++ "/2^" ++ show n

instance Ord Dyadic where
  compare a b = compare (toRational a) (toRational b)

instance Real Dyadic where
  toRational (Dy (a,n)) = (toInteger a)%(2^n)

instance Num Dyadic where
  (Dy (a,n)) + (Dy (b,m))
    | a == 0 = canonicalize $ Dy (b,m)
    | b == 0 = canonicalize $ Dy (a,n)
    | n == m = canonicalize $ Dy ((a + b) `div` 2, n-1)
    | otherwise =
      let n' = max n m in
        canonicalize $ Dy (a * 2^(n' - n) + b * 2^(n' - m), n')
  (Dy (a,n)) * (Dy (b,m)) = canonicalize $ Dy (a * b, n + m)
  negate (Dy (a,n))       = canonicalize $ Dy (-a,n)
  abs (Dy (a,n))          = Dy (a,n)
  signum (Dy (a,n))       = Dy (0,0)
  fromInteger i           = Dy (0,0)

instance Abelian Dyadic where
  zero             = Dy (0,0)
  pow i (Dy (a,n)) = canonicalize $ Dy ((fromInteger i)*a,n)

instance Periodic Dyadic where
  order (Dy (a,n)) = 2^n

instance Ring Dyadic where
  one  = Dy (1,0)

-- TODO: replace with fast log base 2
canonicalize :: Dyadic -> Dyadic
canonicalize (Dy (a,n))
  | a == 0                  = Dy (0,0)
  | a <  0                  = canonicalize $ Dy (2^n + a, n)
  | a `mod` 2 == 0 && n > 0 = canonicalize $ Dy (a `div` 2, n-1)
  | otherwise               = Dy (a `mod` 2^n, n)

dyadic :: Int -> Int -> Dyadic
dyadic a n = canonicalize $ Dy (a,n)

toDouble :: Dyadic -> Double
toDouble (Dy (a,n)) = (fromIntegral a)/2^n
