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
import qualified Feynman.Util.Unicode as Unicode

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

-- | Divide one monomial by another
divM :: Ord v => Monomial v repr -> Monomial v repr -> Monomial v repr
divM m n = Monomial $ Set.difference (vars m) (vars n)

{-------------------------------
 Polynomial reduction over Fields
 -------------------------------}

-- | S-polynomial
sPoly :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
sPoly p q = fromMaybe 0 go where
  go = do
    (a, m) <- leadingTerm p
    (b, n) <- leadingTerm q
    return $ ofTerm (recip a, divM n m) * p - ofTerm (recip b, divM m n) * q

-- | Retrieve the first reducible monomial in f with respect to a monomial
reducible :: (Ord v, Eq r, Fractional r) => (r, Monomial v repr) -> Multilinear v r repr -> Maybe (r, Monomial v repr)
reducible (c, m) = find reducible . toTermList where
  reducible (d, n) = vars m `Set.isSubsetOf` vars n

-- | Retrieve the 
leadReducible :: (Ord v, Eq r, Fractional r) => (r, Monomial v repr) -> Multilinear v r repr -> Maybe (r, Monomial v repr)
leadReducible (c, m) = find reducible . take 1 . toTermList where
  reducible (d, n) = vars m `Set.isSubsetOf` vars n

-- | Reduce a polynomial with respect to another
reduce :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
reduce 0 _ = 0
reduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- reducible (c, m) f
    return $ f - (ofTerm (d/c, divM n m)) * g

-- | Reduce a polynomial with respect to another's leading term
leadReduce :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> PseudoBoolean v r -> PseudoBoolean v r
leadReduce 0 _ = 0
leadReduce f g = fromMaybe f $ go f g where
  go f g = do
    (c, m) <- leadingTerm g
    (d, n) <- leadReducible (c, m) f
    return $ f - (ofTerm (d/c, divM n m)) * g

-- | Compute the fixpoint of a reduction
fixR :: (Ord v, Eq r, Fractional r) => PseudoBoolean v r -> [PseudoBoolean v r] -> PseudoBoolean v r
fixR s xs = case foldl' reduce s xs of
  s' | s == s'   -> s'
     | otherwise -> fixR s' xs

-- | Buchberger's algorithm
buchberger :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> [PseudoBoolean v r]
buchberger xs = go xs [(p, q) | (p:qs) <- tails xs, q <- qs] where
  go basis []         = basis
  go basis ((p,q):xs) =
    let s = sPoly p q in
      case fixR s basis of
        0  -> go basis xs
        s' -> go (s':basis) (xs ++ [(s', p) | p <- basis])

-- | Buchberger's algorithm, restricted to
addToBasis :: (Ord v, Eq r, Fractional r) => [PseudoBoolean v r] -> PseudoBoolean v r -> [PseudoBoolean v r]
addToBasis xs p = go (xs ++ [p]) xs where
  go basis []     = basis
  go basis (q:xs) =
    let s = sPoly p q in
      case fixR s basis of
        0  -> go basis xs
        s' -> go (s':basis) (xs ++ [s' | p <- basis])

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
