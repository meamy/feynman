module Feynman.Algebra.Base where

import Data.Bits
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

{- Finite groups -}
newtype Z2 = Z2 Bool deriving (Eq, Ord)

instance Show Z2 where
  show (Z2 False) = "0"
  show (Z2 True)  = "1"

instance Num Z2 where
  (Z2 x) + (Z2 y) = Z2 $ x `xor` y
  (Z2 x) * (Z2 y) = Z2 $ x && y
  negate        = id
  abs           = id
  signum        = id
  fromInteger i = if i `mod` 2 == 0 then Z2 False else Z2 True

instance Abelian Z2 where
  zero  = Z2 False
  pow i = if i `mod` 2 == 0 then \x -> Z2 False else id

instance Periodic Z2 where
  order (Z2 False) = 1
  order (Z2 True)  = 2

instance Ring Z2 where
  one = Z2 True

instance Fractional Z2 where
  recip          = id
  (/)            = (*)
  fromRational i = fromInteger (numerator i) / fromInteger (denominator i)

instance Field Z2

injectZ2 :: Periodic a => a -> Maybe Z2
injectZ2 a = case order a of
  1 -> Just $ Z2 False
  2 -> Just $ Z2 True
  _ -> Nothing

{- Circle groups -}

-- The "ring" D/Z
-- TODO: Separate D and D/2Z group. Some nasty bugs may come up here
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
  one = Dy (1,0) -- not canonical

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

{- D[e^{2 pi i / 8}] -}
-- TODO: replace with cyclotomic polynomials of arbitrary order.
-- Doesn't really work right now anyway as Dyadic refers to D/Z not D.
newtype DOmega = DOmega (Dyadic, Dyadic, Dyadic, Dyadic) deriving (Eq)

instance Show DOmega where
  show (DOmega (a,b,c,d)) =
    show a ++ " + " ++
    show b ++ "*w + " ++
    show c ++ "*w^2 + " ++
    show d ++ "*w^3"

instance Num DOmega where
  DOmega (a,b,c,d) + DOmega (a',b',c',d') = DOmega (a+a',b+b',c+c',d+d')
  DOmega (a,b,c,d) * DOmega (a',b',c',d') = DOmega (a'',b'',c'',d'')
    where a'' = a*a' - b*d' - c*c' - d*b'
          b'' = a*b' + b*a' - c*d' - d*c'
          c'' = a*c' + b*b' + c*a' - d*d'
          d'' = a*d' + b*c' + c*b' + d*a'
  negate (DOmega (a,b,c,d)) = DOmega (-a,-b,-c,-d)
  abs    x = x -- N/A
  signum x = x -- N/A
  fromInteger i = DOmega (fromInteger i, zero, zero, zero)

instance Abelian DOmega where
  zero  = fromInteger 0
  pow i = scaleD (fromInteger i)

instance Ring DOmega where
  one = fromInteger 1

omega = DOmega(0, Dy (1,0), 0, 0)

-- Unsafe conversions

-- w^x
expZ8 :: Dyadic -> DOmega
expZ8 (Dy (a, n))
  | n > 3  = error "FATAL: can't exponentiate dyadic integers of order greater than 8"
  | n < 3  = expZ8 (Dy (2^(3-n) * a, 3))
  | n == 3 = case a `mod` 4 of
      0 -> DOmega (Dy (y,0), Dy (0,0), Dy (0,0), Dy (0,0))
      1 -> DOmega (Dy (0,0), Dy (y,0), Dy (0,0), Dy (0,0))
      2 -> DOmega (Dy (0,0), Dy (0,0), Dy (y,0), Dy (0,0))
      3 -> DOmega (Dy (0,0), Dy (0,0), Dy (0,0), Dy (y,0))
    where y = (-1)^(a `div` 4)

scaleD :: Dyadic -> DOmega -> DOmega
scaleD x (DOmega (a,b,c,d)) = DOmega (x*a,x*b,x*c,x*d)

-- 1/sqrt(2)^i * w^x
scaledExp :: Int -> Dyadic -> DOmega
scaledExp i d
  | i `mod` 2 == 0 = scaleD (dyadic 1 (i `div` 2)) (expZ8 d)
  | otherwise      = (omega - omega^3) * (scaledExp (i+1) d)
