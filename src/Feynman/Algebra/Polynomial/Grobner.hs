{-|
Module      : Grobner Bases
Description : Tools for Grobner basis calculations
Copyright   : (c) Matthew Amy, 2022
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Grobner where

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import qualified Feynman.Util.Unicode as Unicode

{-------------------------------
 Utilities
 -------------------------------}

-- | Retrieve the leading term
leadingTerm :: (Ring r, Monomial m) => Polynomial r m -> Maybe (r, m)
leadingTerm 0 = Nothing
leadingTerm p = Just . head . reverse . toTermList $ p

-- | Retrieve the leading monomial
leadingMonomial :: (Ring r, Monomial m) => Polynomial r m -> Maybe m
leadingMonomial = fmap snd . leadingTerm

-- | Retrieve the leading coefficient
leadingCoefficient :: (Ring r, Monomial m) => Polynomial r m -> Maybe r
leadingCoefficient = fmap fst . leadingTerm

-- | Decompose into the leading term and the remainder
decomposeLeading :: (Ring r, Monomial m) => Polynomial r m -> (Polynomial r m, Polynomial r m)
decomposeLeading p = case leadingTerm p of
  Nothing -> (0, p)
  Just lt -> (ofTerm lt, p - ofTerm lt)
  
{-------------------------------
 Polynomial reduction over Fields
 -------------------------------}

-- | S-polynomial
sPoly :: (Monomial m, Field r) => Polynomial r m -> Polynomial r m -> Polynomial r m
sPoly p q = fromMaybe 0 go where
  go = do
    (a, m) <- leadingTerm p
    (b, n) <- leadingTerm q
    let lc = leastCM m n
    return $ ofTerm (recip a, lc ./. m) * p - ofTerm (recip b, lc ./. n) * q

-- | Retrieve the first reducible monomial in f with respect to a monomial
reducible :: (Monomial m, Field r) => (r, m) -> Polynomial r m -> Maybe (r, m)
reducible (c, m) = find ((m `divides`) . snd) . reverse . toTermList

-- | Retrieve the lead reducible
lReducible :: (Monomial m, Field r) => (r, m) -> Polynomial r m -> Maybe (r, m)
lReducible (c, m) = find ((m `divides`) . snd) . take 1 . reverse . toTermList

-- | Reduce a polynomial with respect to another
reduce :: (Monomial m, Field r) => Polynomial r m -> Polynomial r m -> Polynomial r m
reduce 0 _ = 0
reduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- reducible (c, m) f
    return $ f - (ofTerm (d/c, n ./. m)) * g

-- | Reduce a polynomial with respect to another's leading term
lReduce :: (Monomial m, Field r) => Polynomial r m -> Polynomial r m -> Polynomial r m
lReduce 0 _ = 0
lReduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- lReducible (c, m) f
    return $ f - (ofTerm (d/c, n ./. m)) * g

-- | Divides a polynomial with respect to the ideal generated by a list
mvd :: (Monomial m, Field r) => Polynomial r m -> [Polynomial r m] -> Polynomial r m
mvd f xs = go f xs where
  go 0 _  = 0
  go f xs =
    let f' = foldl' lReduce f xs in
      if f == f' then (\(r,p) -> r + go p xs) $ decomposeLeading f
      else go f' xs

-- | Buchberger's iterative algorithm
addToBasis :: (Monomial m, Field r) => [Polynomial r m] -> Polynomial r m -> [Polynomial r m]
addToBasis xs p = go (xs ++ [p]) (zip (repeat p) xs) where
  go basis []     = basis
  go basis ((p,q):xs) =
    let s = sPoly p q in
      case mvd s basis of
        0  -> go basis xs
        s' -> go (basis ++ [s']) (xs ++ [(s',p) | p <- basis])

-- | Buchberger's algorithm
buchberger :: (Monomial m, Field r) => [Polynomial r m] -> [Polynomial r m]
buchberger = foldl' addToBasis []

-- | Reduces an existing Grobner basis
reduceBasis :: (Monomial m, Ord r, Field r) => Set (Polynomial r m) -> Set (Polynomial r m)
reduceBasis gbasis = Set.fold go Set.empty gbasis where
  go p          = Set.insert (squashCoeff $ mvd p (Set.toList $ Set.delete p gbasis))
  squashCoeff p = scale (recip . fromMaybe 1 $ leadingCoefficient p) p

-- | Produces a relatively reduced basis
addToRBasis :: (Monomial m, Ord r, Field r) => Set (Polynomial r m) -> Polynomial r m -> Set (Polynomial r m)
addToRBasis basis p = go (Set.insert p' basis) (zip (repeat p') $ Set.toList basis) where
  squashCoeff q = scale (recip . fromMaybe 1 $ leadingCoefficient q) q
  p' = squashCoeff $ mvd p (Set.toList basis)
  go basis []         = basis
  go basis ((p,q):xs) =
    let s = sPoly p q in
      case mvd s (Set.toList basis) of
        0  -> go basis xs
        s' -> let s'' = squashCoeff s'
                  basis' = Set.map (flip reduce $ s'') basis
              in
          go (Set.insert s'' basis') (xs ++ [(s'',p) | p <- Set.toList basis'])

-- | Buchberger's algorithm
rBuchberger :: (Monomial m, Ord r, Field r) => [Polynomial r m] -> Set (Polynomial r m)
rBuchberger = foldl' addToRBasis Set.empty

-- Testing

newtype IVar = IVar (String, Integer) deriving (Eq, Ord)

instance Show IVar where
  show (IVar (x, i)) = Unicode.sub x i
newtype SVar = SVar String deriving (Eq)

instance Ring FF2
instance Field FF2

instance Ring Double
instance Field Double

type IMonomial = GrevlexPP IVar
type IPolynomial = Polynomial Double IMonomial

x0 = ofVar (IVar ("x",0)) :: IPolynomial
x1 = ofVar (IVar ("x",1)) :: IPolynomial
x2 = ofVar (IVar ("x",2)) :: IPolynomial
x3 = ofVar (IVar ("x",3)) :: IPolynomial
x4 = ofVar (IVar ("x",4)) :: IPolynomial
x5 = ofVar (IVar ("x",5)) :: IPolynomial
x6 = ofVar (IVar ("x",6)) :: IPolynomial
x7 = ofVar (IVar ("x",7)) :: IPolynomial
x8 = ofVar (IVar ("x",8)) :: IPolynomial
x9 = ofVar (IVar ("x",9)) :: IPolynomial

p1 = x0*x0 + x0
p2 = x1*x1 + x1
p3 = x2*x2 + x2
p4 = x3*x3 + x3
p5 = x0*x1 + x0 + x1 + 1
p6 = x2*x3 + x2 + x3 + 1
p7 = x0*x3
p8 = x0*x2
p9 = x1*x3
p10 = x1*x2 + 1

i0 = [p1,p2,p3,p4,p5,p6,p7,p8,p9]
i1 = [p1,p2,p3,p4,p5,p6,p7,p8,p9,p10]

i2 = [x0*x0*x0 - scale 2 (x0*x1), x0*x0*x1 - scale 2 (x1*x1) + x0]