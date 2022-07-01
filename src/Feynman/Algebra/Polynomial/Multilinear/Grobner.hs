{-|
Module      : Multilinear Grobner Bases
Description : Tools for Grobner basis calculations over multilinear polynomials
Copyright   : (c) Matthew Amy, 2022
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Multilinear.Grobner where

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
 Polynomial reduction
 -------------------------------}

-- | Retrieve the first reducible monomial in f with respect to 
reductionTerm :: (Ord v, Eq r, Euclidean r) => (r, Monomial v repr) -> Multilinear v r repr -> Maybe (r, Monomial v repr)
reductionTerm (c, m) = find reducible . toTermList where
  reducible (d, n) = fst (divmod d c) /= 0 && vars m `Set.isSubsetOf` vars n

-- | Reduce a polynomial with respect to another
reduce :: (Ord v, Eq r, Euclidean r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
reduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- reductionTerm (c, m) f
    (q, r) <- return $ divmod d c
    t      <- return $ Monomial $ Set.difference (vars n) (vars m)
    return $ (f - ofTerm (d, n)) + ofTerm (r, n) + ofTerm (q, t) * (ofTerm (c, m) - g)
    
