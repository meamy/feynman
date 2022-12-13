{-|
Module      : Multilinear Grobner Bases over Euclidean domains
Description : Grobner basis calculations in the case of Euclidean domains
Copyright   : (c) Matthew Amy, 2022
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Multilinear.Grobner.Euclidean where

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear

{-------------------------------
 Utilities
 -------------------------------}

-- | Retrieve the leading term
leadingTerm :: Ord v => Multilinear v r repr -> Maybe (r, Monomial v repr)
leadingTerm = find ((/= Monomial Set.empty) . snd) . toTermList

-- | Retrieve the leading monomial
leadingMonomial :: Ord v => Multilinear v r repr -> Maybe (Monomial v repr)
leadingMonomial = fmap snd . leadingTerm

-- | Retrieve the leading coefficient
leadingCoefficient :: Ord v => Multilinear v r repr -> Maybe r
leadingCoefficient = fmap fst . leadingTerm

{-------------------------------
 Polynomial reduction over
 Euclidean domains
 -------------------------------}

-- | Retrieve the first reducible monomial in f with respect to 
reductionTerm :: (Ord v, Eq r, Euclidean r) => (r, Monomial v repr) -> Multilinear v r repr -> Maybe (r, Monomial v repr)
reductionTerm (c, m) = find reducible . toTermList where
  reducible (d, n) = fst (divmod d c) /= 0 && vars m `Set.isSubsetOf` vars n

-- | Reduce a polynomial with respect to another
reduce :: (Ord v, Eq r, Euclidean r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
reduce 0 _ = 0
reduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- reductionTerm (c, m) f
    (q, r) <- return $ divmod d c
    t      <- return $ Monomial $ Set.difference (vars n) (vars m)
    return $ (f - ofTerm (d, n)) + ofTerm (r, n) + ofTerm (q, t) * (ofTerm (c, m) - g)
    
-- | Reduce relative to a set of polynomials
reduceAll :: (Ord v, Eq r, Euclidean r) => PseudoBoolean v r -> [PseudoBoolean v r] -> PseudoBoolean v r
reduceAll = foldl' reduce

-- | Critical pair computation
criticalPair :: (Ord v, Eq r, Euclidean r) => PseudoBoolean v r -> PseudoBoolean v r -> Maybe (PseudoBoolean v r, PseudoBoolean v r)
criticalPair p q = do
  (c1, m1) <- leadingTerm p
  (c2, m2) <- leadingTerm q
  (a, b)   <- return $ if rank c1 >= rank c2 then divmod c1 c2 else divmod c2 c1
  f1       <- return $ Monomial $ Set.difference (vars m2) (vars m1)
  f2       <- return $ Monomial $ Set.difference (vars m1) (vars m2)
  if rank c1 >= rank c2 then
    return (ofTerm (a, f2) * (ofTerm (c2, m2) - q) + ofTerm (b, m1 <> m2),
            ofTerm (1, f1) * (ofTerm (c1, m1) - p))
  else
    return (ofTerm (a, f1) * (ofTerm (c1, m1) - p) + ofTerm (b, m1 <> m2),
            ofTerm (1, f2) * (ofTerm (c2, m2) - q))

-- | S-polynomial
sPoly :: (Ord v, Eq r, Euclidean r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
sPoly p = maybe 0 (\(p, q) -> p - q) . criticalPair p

-- | Buchberger's algorithm
buchberger :: (Ord v, Eq r, Euclidean r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
buchberger xs = go xs [(p, q) | p <- xs, q <- xs, p /= q] where
  go basis []         = basis
  go basis ((p,q):xs) =
    let s = sPoly p q in
      case reduceAll s basis of
        0  -> go basis xs
        s' -> go (s:basis) (xs ++ [(p, s) | p <- basis])

-- | Buchberger's algorithm, restricted to
addToBasis :: (Ord v, Eq r, Euclidean r) => [PseudoBoolean v r] -> PseudoBoolean v r -> [PseudoBoolean v r]
addToBasis xs p = go (xs ++ [p]) xs where
  go basis []     = basis
  go basis (q:xs) =
    let s = sPoly p q in
      case reduceAll s basis of
        0  -> go basis xs
        s' -> go (s:basis) (xs ++ [s | p <- basis])
