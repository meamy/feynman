import Prelude hiding ((+), (*))
import qualified Prelude as Prelude

class Abelian a where
  zero   :: a
  (+)    :: a -> a -> a
  negate :: a -> a
  pow    :: Int -> a -> a

instance (Num a) => (Abelian a) where
  zero    = Prelude.fromInteger
  (+)     = Prelude.(+)
  negate  = Prelude.negate
  pow k x = Prelude.(*) (Prelude.fromInteger k) x

class Abelian a => Ring a where
  one :: a
  (*) :: a -> a -> a
