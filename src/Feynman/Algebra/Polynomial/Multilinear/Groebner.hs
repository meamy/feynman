{-|
Module      : Multilinear Groebner Bases
Description : Tools for Groebner basis calculations over multilinear polynomials
Copyright   : (c) Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Multilinear.Groebner where

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import qualified Feynman.Util.Unicode as Unicode

{-------------------------------
 Utilities
 -------------------------------}

-- | Retrieve the leading term
leadingTerm :: (Ord v, Eq r, Num r) => PseudoBoolean v r -> (r, PowerProduct v)
leadingTerm 0 = (0, Monomial Set.empty)
leadingTerm p = head . reverse . toTermList $ p

-- | Retrieve the leading monomial
leadingMonomial :: (Ord v, Eq r, Num r) => PseudoBoolean v r -> (PowerProduct v)
leadingMonomial = snd . leadingTerm

-- | Retrieve the leading coefficient
leadingCoefficient :: (Ord v, Eq r, Num r) => PseudoBoolean v r -> r
leadingCoefficient = fst . leadingTerm

-- | Decompose into the leading term and the remainder
decomposeLeading :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> (PseudoBoolean v r, PseudoBoolean v r)
decomposeLeading p = (ofTerm lt, p - ofTerm lt)
  where lt = leadingTerm p

-- | Divide one monomial by another. /m/ must be divisible by /n/
coprime :: Ord v => PowerProduct v -> PowerProduct v -> Bool
coprime m n = Set.intersection (vars m) (vars n) == Set.empty

-- | Determines whether one monomial is divisible by another
divides :: Ord v => PowerProduct v -> PowerProduct v -> Bool
divides m n = vars m `Set.isSubsetOf` vars n

-- | Divide one monomial by another. /m/ must be divisible by /n/
divide :: Ord v => PowerProduct v -> PowerProduct v -> PowerProduct v
divide m n = Monomial $ Set.difference (vars m) (vars n)

{-------------------------------
 Polynomial reduction over Fields
 -------------------------------}

-- | S-polynomial
sPoly :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
sPoly p q = ofTerm (recip a, divide lc m) * p - ofTerm (recip b, divide lc n) * q
  where (a, m) = leadingTerm p
        (b, n) = leadingTerm q
        lc     = m <> n

-- | Retrieve the first reducible monomial in f with respect to a monomial
reducible :: (Ord v, Eq r, Fractional r) => (r, PowerProduct v) -> PseudoBoolean v r -> Maybe (r, PowerProduct v)
reducible (c, m) = find (\(_d, n) -> m `divides` n) . toTermList

-- | Retrieve the 
leadReducible :: (Ord v, Eq r, Fractional r) => (r, PowerProduct v) -> PseudoBoolean v r -> Maybe (r, PowerProduct v)
leadReducible (c, m) = find (\(_d, n) -> m `divides` n) . take 1 . toTermList

-- | Reduce a polynomial with respect to another
reduce :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
reduce 0 _ = 0
reduce f g = fromMaybe f $ go f g where
  go f g = do
    let (c, m) = leadingTerm g
    (d, n) <- reducible (c, m) f
    return $ f - (ofTerm (d/c, divide n m)) * g

-- | Reduce a polynomial with respect to another's leading term
leadReduce :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
leadReduce f g
  | f == 0        = 0
  | m `divides` n = f - (ofTerm (d/c, divide n m)) * g
  | otherwise     = f
  where (c, m) = leadingTerm g
        (d, n) = leadingTerm f

-- | Compute the fixpoint of a reduction
mvd :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> [PseudoBoolean v r] -> PseudoBoolean v r
mvd f xs = go f xs where
  go 0 _  = 0
  go f xs =
    let f' = foldl' leadReduce f xs in
      if f == f' then (\(r,p) -> r + go p xs) $ decomposeLeading f
      else go f' xs

-- | Buchberger's iterative algorithm for multilinear polynomial rings
--
--   Rather than include the quadratic polynomials x^2 - x in the basis, we include them implicitly
--   and add the implicit (multilinear) S-polynomials they generate, (p - LT(p))*v - LT(p)
addToBasis :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> PseudoBoolean v r -> [PseudoBoolean v r]
addToBasis xs p = go (xs ++ [p]) (sPolys p xs) where
  nonzero p q = not $ coprime (leadingMonomial p) (leadingMonomial q)
  sPolys p xs = qfPolys p ++ [sPoly p q | q <- xs, nonzero p q]
  qfPolys     = map (\v -> ofVar v * p) . Set.toList . vars . leadingMonomial
  go basis []     = basis
  go basis (s:xs) = case mvd s basis of
    0  -> go basis xs
    s' -> go (basis ++ [s']) (xs ++ (sPolys s' basis))

-- | Buchberger's algorithm
buchberger :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
buchberger = foldl' addToBasis []

-- | Reduces an existing Groebner basis
reduceBasis :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
reduceBasis gbasis = go [] gbasis where
  squashCoeff p         = scale (recip $ leadingCoefficient p) p
  go gbasis' []         = gbasis'
  go gbasis' (p:gbasis) = case squashCoeff $ mvd p (gbasis' ++ gbasis) of
    0  -> go gbasis' gbasis
    p' -> go (p':gbasis') gbasis

-- | Buchberger's algorithm, modified to return a reduced Groebner basis
rbuchberger :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
rbuchberger = foldl' (\x -> reduceBasis . addToBasis x) []

-- Testing

newtype IVar = IVar (String, Integer) deriving (Eq, Ord)

instance Show IVar where
  show (IVar (x, i)) = Unicode.sub x i

x0 = ofVar (IVar ("x",0)) :: SBool IVar
x1 = ofVar (IVar ("x",1)) :: SBool IVar
x2 = ofVar (IVar ("x",2)) :: SBool IVar
x3 = ofVar (IVar ("x",3)) :: SBool IVar
x4 = ofVar (IVar ("x",4)) :: SBool IVar
x5 = ofVar (IVar ("x",5)) :: SBool IVar
x6 = ofVar (IVar ("x",6)) :: SBool IVar
x7 = ofVar (IVar ("x",7)) :: SBool IVar
x8 = ofVar (IVar ("x",8)) :: SBool IVar
x9 = ofVar (IVar ("x",9)) :: SBool IVar

i1 = [x0*x1 + x0 + x1 + 1,
      x2*x3 + x2 + x3 + 1,
      x0*x3,
      x0*x2,
      x1*x3,
      x1*x2 + 1]

y0 = ofVar (IVar ("y",0)) :: PseudoBoolean IVar Double
y1 = ofVar (IVar ("y",1)) :: PseudoBoolean IVar Double
y2 = ofVar (IVar ("y",2)) :: PseudoBoolean IVar Double
y3 = ofVar (IVar ("y",3)) :: PseudoBoolean IVar Double
y4 = ofVar (IVar ("y",4)) :: PseudoBoolean IVar Double
y5 = ofVar (IVar ("y",5)) :: PseudoBoolean IVar Double
y6 = ofVar (IVar ("y",6)) :: PseudoBoolean IVar Double
y7 = ofVar (IVar ("y",7)) :: PseudoBoolean IVar Double
y8 = ofVar (IVar ("y",8)) :: PseudoBoolean IVar Double
y9 = ofVar (IVar ("y",9)) :: PseudoBoolean IVar Double

i2 = [y0*y1 + y0 + y1 + 1,
      y2*y3 + y2 + y3 + 1,
      y0*y3,
      y0*y2,
      y1*y3,
      y1*y2 + 1]
