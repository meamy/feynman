{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Feynman.Algebra.Abstract where

import Prelude hiding ((+), (*), (-), (/))
import qualified Prelude as Prelude

import GHC.TypeLits
import Data.Proxy

import Data.Bits

{- Abelian groups -}
class Abelian a where
  zero   :: a
  (+)    :: a -> a -> a
  (-)    :: a -> a -> a
  neg :: a -> a
  pow    :: Integer -> a -> a
    -- Minimal complete definition:
    --   zero, two of (+), (-), neg
  x + y   = x - (neg y)
  x - y   = x + (neg y)
  neg x   = zero - x
  pow i x = (iterate (+ x) zero)!!(fromInteger i)

class Abelian a => Periodic a where
  order :: a -> Int

{- Rings -}
class Abelian a => Ring a where
  one :: a
  (*) :: a -> a -> a

{- Fields -}
class Ring a => Field a where
  inv :: a -> a
  (/) :: a -> a -> a
    -- Minimal complete definition:
    --   One of inv, (/)
  inv x = one / x
  x / y = x * (inv y)

{- Providing builtin operators -}
instance Abelian Int where
  zero    = fromInteger 0
  (+)     = (Prelude.+)
  neg     = negate
  pow k x = (Prelude.*) (fromInteger k) x

instance Ring Int where
  one = fromInteger 1
  (*) = (Prelude.*)

instance Abelian Float where
  zero    = fromInteger 0
  (+)     = (Prelude.+)
  neg     = negate
  pow k x = (Prelude.*) (fromInteger k) x
  
instance Ring Float where
  one = fromInteger 1
  (*) = (Prelude.*)

instance Field Float where
  inv = recip
  (/) = (Prelude./)

{- Finite groups -}

-- Note: For efficiency it would be preferable to have a data family, but at the
-- moment it's unclear how since GHC checks constraints after instance choice
data Zmod (n :: Nat) where
  ZN :: (KnownNat n) => Int -> Zmod n

instance Show (Zmod n) where
  show (ZN i) = show i

instance (KnownNat n) => Abelian (Zmod n) where
  zero            = ZN 0
  (ZN x) + (ZN y) = ZN $ (x + y) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  (ZN x) - (ZN y) = ZN $ (x - y) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  neg (ZN x)      = ZN $ (-x) `mod` (fromInteger $ natVal (Proxy::Proxy n))
  pow i (ZN x)    = ZN $ (fromInteger i) * x `mod` (fromInteger $ natVal (Proxy::Proxy n))

instance (KnownNat n) => Periodic (Zmod n) where
  order (ZN x) = (lcm x (fromInteger $ natVal (Proxy::Proxy n))) `div` x

inject :: (KnownNat n) => Integer -> Zmod n
inject i = result
  where result = ZN $ (fromInteger i) `mod` (fromInteger $ natVal result)

tmp = inject 3 :: Zmod 8

{- Numeric instance for Boolean polynomials -}
-- NOTE: "from" functions aren't homomorphic
{-
instance Num Bool where
  (+)           = xor
  (*)           = (&&)
  negate        = id
  abs           = id
  signum        = id
  fromInteger i = if i `mod` 2 == 0 then False else True

instance Fractional Bool where
  recip          = id
  (/)            = (*)
  fromRational i = fromInteger (numerator i) / fromInteger (denominator i)

newtype Z8 = Z8 { inject :: Int } deriving (Eq)

instance Show Z8 where
  show (Z8 x) = show x

instance Abelian Z8 where
  (Z8 x) + (Z8 y) = Z8 $ (x + y) `mod` 8
  (Z8 x) * (Z8 y) = Z8 $ (x * y) `mod` 8
  negate (Z8 x)   = Z8 $ 8 - x
  abs (Z8 x)      = Z8 $ x `mod` 8
  signum (Z8 x)   = Z8 $ signum x
  fromInteger i   = Z8 $ fromIntegral $ i `mod` 8

instance Fin Z8 where
  order (Z8 x) = (lcm x 8) `div` x

injectZ2 :: Fin a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing
-}

{- Circle groups -}
newtype D = D (Int, Int) deriving (Eq) -- NOTE: must be in lowest form

instance Show D where
  show (D (a,n)) = show a ++ "/2^" ++ show n

instance Abelian D where
  zero = D (0,0)
  (D (a,n)) + (D (b,m))
    | a == 0 = D (b,m)
    | b == 0 = D (a,n)
    | n == m = canonicalize $ D ((a + b) `div` 2, n-1)
    | otherwise =
      let n' = max n m in
        canonicalize $ D (a * 2^(n' - n) + b * 2^(n' - m), n')
  neg (D (a,n))   = D (-a, n)
  pow i (D (a,n)) = canonicalize $ D ((fromInteger i) * a, n)

instance Periodic D where
  order (D (a,n)) = 2^n

instance Ring D where
  one                   = D (1,0)
  (D (a,n)) * (D (b,m)) = canonicalize $ D (a * b, n + m)

-- TODO: replace with fast log base 2
canonicalize :: D -> D
canonicalize (D (a,n))
  | a == 0                  = D (0,0)
  | a `mod` 2 == 0 && n > 0 = canonicalize $ D (a `div` 2, n-1)
  | otherwise               = D (a,n)

{- Polynomial rings -}

{-
newtype DOmega    = DOmega (DyadicInt, DyadicInt, DyadicInt, DyadicInt) deriving (Eq)

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
  fromInteger i = DOmega (fromInteger i, D (0,0), D (0,0), D (0,0))

-- w^x
expZ8 :: Z8 -> DOmega
expZ8 (Z8 x) = case x `mod` 4 of
  0 -> DOmega (D (y,0), D (0,0), D (0,0), D (0,0))
  1 -> DOmega (D (0,0), D (y,0), D (0,0), D (0,0))
  2 -> DOmega (D (0,0), D (0,0), D (y,0), D (0,0))
  3 -> DOmega (D (0,0), D (0,0), D (0,0), D (y,0))
  where y = (-1)^(x `div` 4)

scaleD :: DyadicInt -> DOmega -> DOmega
scaleD x (DOmega (a,b,c,d)) = DOmega (x*a,x*b,x*c,x*d)

-- 1/sqrt(2)^i * w^x
scaledExp :: Int -> Z8 -> DOmega
scaledExp i (Z8 x)
  | i `mod` 2 == 0 = scaleD (D (1,i `div` 2)) (expZ8 $ Z8 x)
  | otherwise      = scaledExp (i+1) (Z8 $ mod (x-1) 8) + scaledExp (i+1) (Z8 $ mod (x+1) 8)
-}
