{-# LANGUAGE UndecidableInstances #-}
module Algebra.Abstract where

import Prelude hiding ((+), (*), (-), negate)
import qualified Prelude as Prelude


{- Abelian groups -}
class Abelian a where
  zero   :: a
  (+)    :: a -> a -> a
  (-)    :: a -> a -> a
  negate :: a -> a
  pow    :: Integer -> a -> a
    -- Minimal complete definition:
    --   zero, two of (+), (-), negate
  x + y    = x - (negate y)
  x - y    = x + (negate y)
  negate x = zero - x
  pow i x  = (iterate (+ x) zero)!!(fromInteger i)

instance Abelian Int where
  zero    = Prelude.fromInteger 0
  (+)     = (Prelude.+)
  negate  = Prelude.negate
  pow k x = (Prelude.*) (Prelude.fromInteger k) x

{- Rings -}
class Abelian a => Ring a where
  one :: a
  (*) :: a -> a -> a

instance Ring Int where
  one = Prelude.fromInteger 1
  (*) = (Prelude.*)
