module Specs.AlgebraLinearSpec where

import Control.Monad
import Control.Monad.Writer
import Data.Bits (popCount)
import Data.Set (Set)
import qualified Data.Set as Set

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Feynman.Algebra.Linear
import Feynman.Algebra.Matroid

rowRange = (10, 100)
colRange = (10, 100)

instance Arbitrary F2Mat where
  arbitrary = do
    m <- choose rowRange
    n <- choose colRange
    let genRow = (vector n) >>= return . fromBits
    vals <- sequence $ replicate m genRow
    return $ F2Mat m n vals

arbitraryFixedN, arbitraryFixedM :: Int -> Gen F2Mat
arbitraryFixedN n = do
  m <- choose rowRange
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals
arbitraryFixedM m = do
  n <- choose colRange
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

arbitraryFixed :: Int -> Int -> Gen F2Mat
arbitraryFixed m n = do
  let genRow = (vector n) >>= return . fromBits
  vals <- sequence $ replicate m genRow
  return $ F2Mat m n vals

-- Generate a matrix whose rowspace is a subspace of it's argument's
arbitrarySubspace :: F2Mat -> Gen F2Mat
arbitrarySubspace a =
  liftM (multT a) $ arbitraryFixed (m a) (m a)

{- Properties of unary operators -}
invol, idemp :: Eq a => (a -> a) -> (a -> Bool)

invol f = \a -> a == (f $ f a)
idemp f = \a -> (f a) == (f $ f a)

{- Properties of binary operators -}
lid, rid   :: Eq a => (a -> a -> a) -> a -> (a -> Bool)
linv, rinv :: Eq a => (a -> a -> a) -> a -> (a -> a) -> (a -> Bool)
assoc      :: Eq a => (a -> a -> a) -> (a -> a -> a -> Bool)
commut     :: Eq a => (a -> a -> a) -> (a -> a -> Bool)

lid    f i = \a -> f i a == a
rid    f i = \a -> f a i == a
linv   f i inv = \a -> f (inv a) a == i
rinv   f i inv = \a -> f a (inv a) == i
assoc  f = \a b c -> f a (f b c) == f (f a b) c
commut f = \a b   -> f a b == f b a

{- Matrix properties -}
isSquare, isInvertible :: F2Mat -> Bool

isSquare mat = m mat == n mat
isInvertible mat = isSquare mat && rank mat == m mat

prop_TransposeInvolutive = invol transpose
prop_ToEchelonIdempotent = idemp (fst . runWriter . toEchelon)
prop_ToReducedEchelonIdempotent = idemp (fst . runWriter . toReducedEchelon)
prop_MultAssociative = do
  a <- arbitrary
  b <- arbitraryFixedM $ n a
  c <- arbitraryFixedM $ n b
  return $ assoc mult a b c
prop_PseudoinverseCorrect = \m -> m == mult (mult m $ pseudoinverse m) m
prop_TransformMatCorrect = do
  a <- arbitrary
  b <- arbitrarySubspace a
  return $ mult (transformMat a b) a == b

prop_MatroidPartition = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ (Set.fromList vecs) == (foldr Set.union Set.empty $ partitionAll vecs)
prop_MatroidCorrect = do
  a <- arbitrary
  let vecs = filter (\bv -> popCount bv /= 0) $ vals a
  return $ all independent $ partitionAll vecs

spec :: Spec
spec = return ()
specDisabled = do
  prop "transpose is involutive" prop_TransposeInvolutive
  prop "toEchelon is idempotent" prop_ToEchelonIdempotent
  prop "toReducedEchelon is idempotent" prop_ToReducedEchelonIdempotent
  prop "mult is associative" prop_MultAssociative
  prop "pseudoinverse is correct" prop_PseudoinverseCorrect
  prop "transformMat is correct" prop_TransformMatCorrect
  prop "partitionAll is a partition" prop_MatroidPartition
  prop "partitionAll produces independent vectors" prop_MatroidCorrect

