{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Multilinear
Description : Multilinear polynomials & pseudo-Boolean functions
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

Provides tools for working with multilinear polynomials in the
multiplicative and additive "parity" basis.
-}
module Feynman.Algebra.Polynomial.Multilinear where

import Data.Kind
import Data.Tuple
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

import Feynman.Algebra.Base

{-----------------------------------
 Utility types
 -----------------------------------}

-- | Class of things that have a degree
class Degree a where
  degree :: a -> Int

data Repr = Add | Mult
data ReprWit :: Repr -> Type where
  WitAdd  :: ReprWit 'Add
  WitMult :: ReprWit 'Mult

class ReprC repr where
  witRepr :: ReprWit repr

instance ReprC 'Add where
  witRepr = WitAdd

instance ReprC 'Mult where
  witRepr = WitMult

{-----------------------------------
 Monomials
 -----------------------------------}
-- | Variables in polynomials
type Var = String

-- | Monomials with graded lexicographic (grevlex) order
newtype Monomial (repr :: Repr) = Monomial { vars :: Set Var } deriving (Eq)

instance Ord (Monomial repr) where
  compare m n = case compare (degree m) (degree n) of
    EQ -> compare (vars m) (vars n)
    x  -> x

instance Degree (Monomial repr) where
  degree = Set.size . vars

showMonomial :: ReprWit repr -> Monomial repr -> String
showMonomial wit = case wit of
  WitAdd  -> intercalate "\x2295" . Set.toList . vars
  WitMult -> concat . Set.toList . vars

instance ReprC repr => Show (Monomial repr) where
  show = showMonomial witRepr

instance Semigroup (Monomial repr) where
  m <> m' = Monomial $ Set.union (vars m) (vars m')

{-----------------------------------
 Multilinear polynomials
 -----------------------------------}

-- | Multilinear polynomials over a ring /r/ with representation /repr/
data Multilinear r (repr :: Repr) = M { terms :: !(Map (Monomial repr) r) }
  deriving (Eq, Ord)

-- | Convenience types
type PhasePoly r  = Multilinear r 'Add
type PseudoBool r = Multilinear r 'Mult
type BoolPoly     = Multilinear FF2 'Mult

instance (Eq r, Num r, Show r, ReprC repr) => Show (Multilinear r repr) where
  show p@(M t)
    | isZero p  = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs t)
    where showTerm (mono, coeff)
            | degree mono == 0 = show coeff
            | coeff == 1       = show mono
            | coeff == -1      = "-" ++ show mono
            | otherwise        = show coeff ++ show mono

instance Degree (Multilinear r repr) where
  degree (M t) = case Map.lookupMax t of
    Nothing      -> -1
    Just (m, _a) -> degree m

instance (Eq r, Num r, ReprC repr) => Num (Multilinear r repr) where
  (+) = addM
  (*) = multM witRepr
  negate (M t) = M $ Map.map negate t
  abs    p = p
  signum p = p
  fromInteger 0 = M $ Map.empty
  fromInteger i = M . Map.singleton (Monomial Set.empty) $ fromInteger i

{- Accessors -}

-- | Get a list of the coefficients in grevlex order
coefficients :: Multilinear r repr -> [r]
coefficients = Map.elems . terms

-- | Get the terms in grevlex order
toTermList :: Multilinear r repr -> [(r, Monomial repr)]
toTermList = map swap . Map.toList . terms

-- | Get a list of variables contained in the polynomial
varList :: Multilinear r repr -> [Var]
varList = Set.toList . foldr (Set.union) Set.empty . map vars . Map.keys . terms

-- | Retrieve the constant term
getConstant :: (Eq r, Num r) => Multilinear r repr -> r
getConstant = Map.findWithDefault 0 (Monomial Set.empty) . terms

{- Tests -}

-- | Check if the polynomial is the zero function
isZero :: Multilinear r repr -> Bool
isZero = Map.null . terms

-- | Check if the polynomial is a monomial
isMono :: Multilinear r repr -> Bool
isMono = (1 >=) . Map.size . terms

-- | Check if the polynomial is constant
isConst :: Multilinear r repr -> Bool
isConst = (== [Monomial Set.empty]) . Map.keys . terms

-- | Check if a variable is used in the polynomial
contains :: String -> Multilinear r repr -> Bool
contains v = any (Set.member v . vars) . Map.keys . terms

{- Constructors -}

-- | Constant polynomial
constant :: (Eq r, Num r) => r -> Multilinear r repr
constant = normalize . M . Map.singleton (Monomial Set.empty)

-- | Construct the variable polynomial /x/
ofVar :: (Eq r, Num r) => Var -> Multilinear r repr
ofVar x = ofTerm (1, Monomial $ Set.singleton x)

-- | Construct the polynomial /m/ for a monomial /m/
ofMonomial :: (Eq r, Num r) => Monomial repr -> Multilinear r repr
ofMonomial m = ofTerm (1, m)

-- | Construct the polynomial /a*m/
ofTerm :: (Eq r, Num r) => (r, Monomial repr) -> Multilinear r repr
ofTerm (a, m) = normalize . M $ Map.singleton m a

-- | Construct the polynomial /a*m/
ofTermList :: (Eq r, Num r) => [(r, Monomial repr)] -> Multilinear r repr
ofTermList = normalize . M . Map.fromList . map swap

-- | (Internal use only) Construct the polynomial /a*m/
ofTermDirect :: (Eq r, Num r) => (r, Monomial repr) -> Multilinear r repr
ofTermDirect (a, m) = M $ Map.singleton m a

{- Arithmetic -}

-- | Scale a 
scale :: (Eq r, Num r, ReprC repr) => r -> Multilinear r repr -> Multilinear r repr
scale a p
  | a == 0    = zero
  | otherwise = M $ Map.map (a*) $ terms p

-- | Add two polynomials with the same representation
addM :: (Eq r, Num r) => Multilinear r repr -> Multilinear r repr -> Multilinear r repr
addM p q = normalize . M $ Map.unionWith (+) (terms p) (terms q)

-- | Multiply two polynomials with the same representation
multM :: (Eq r, Num r) =>
  ReprWit repr -> Multilinear r repr -> Multilinear r repr -> Multilinear r repr
multM wit p q = case wit of
  WitAdd  -> error "Error: multiplying additive phase polynomials"
  WitMult -> normalize $ multImpl p q

multImpl :: (Eq r, Num r) => Multilinear r 'Mult -> Multilinear r 'Mult -> Multilinear r 'Mult
multImpl p q = Map.foldlWithKey' multPolyTerm zero (terms p)
  where multPolyTerm acc m a =
          addM acc (M $ Map.foldlWithKey' (multTermTerm m a) Map.empty (terms q))
        multTermTerm m a acc m' a' = Map.alter (addCoeff $ a * a') (m <> m') acc
        addCoeff a b = case b of
          Nothing -> Just a
          Just c  -> Just $ a + c

-- | Factorizes a polynomial /p/ as /vq + r/
factorVar :: Var -> Multilinear r 'Mult -> (Multilinear r 'Mult, Multilinear r 'Mult)
factorVar v p = (M qTerms, M rTerms)
  where (qTerms, rTerms) = Map.partitionWithKey (\m _a -> Set.member v $ vars m) $ terms p

-- | Takes the quotient of /p\/v/
divVar :: Var -> Multilinear r 'Mult -> Multilinear r 'Mult
divVar v = M . Map.mapKeys (Monomial . Set.delete v . vars) . takeQuotient . terms
  where takeQuotient = Map.filterWithKey (\m _a -> Set.member v $ vars m)

-- | Takes the quotient of /p\/v/
remVar :: Var -> Multilinear r 'Mult -> Multilinear r 'Mult
remVar v = M . Map.filterWithKey (\m _a -> not $ Set.member v $ vars m) . terms

{- Transformations -}

-- | Normalize a multilinear polynomial
normalize :: (Eq r, Num r) => Multilinear r repr -> Multilinear r repr
normalize = M . Map.filter (0/=) . terms

-- | Drops the constant term. Useful for verification up to global phase
dropConstant :: (Eq r, Num r) => Multilinear r repr -> Multilinear r repr
dropConstant = M . (Map.delete (Monomial Set.empty) . terms)

-- | Cast a polynomial over ring /r/ to ring /s/
cast :: (r -> s) -> Multilinear r repr -> Multilinear s repr
cast f = M . Map.map f . terms

-- | Attempt to cast a polynomial over ring /r/ to ring /s/ via a partial function
castMaybe :: (r -> Maybe s) -> Multilinear r repr -> Maybe (Multilinear s repr)
castMaybe f = fmap M . mapM f . terms

-- | Collects just the terms of the polynomial satisfying a predicate
collectBy :: ((r, Monomial repr) -> Bool) -> Multilinear r repr -> Multilinear r repr
collectBy f = M . Map.filterWithKey (curry $ f . swap) . terms

-- | Collects the terms of a polynomial containing a particular variable
collectVar :: Var -> Multilinear r repr -> Multilinear r repr
collectVar v = collectBy (\(_a, m) -> Set.member v $ vars m)
  
{- Substitutions -}

-- | Rename variables according to a variable map
rename :: (Eq r, Num r) => Map Var Var -> Multilinear r repr -> Multilinear r repr
rename sub = M . Map.mapKeys (Monomial . Set.map substVar . vars) . terms
  where substVar v = Map.findWithDefault v v sub

-- | Rename variables according to a monotonic variable map
renameMonotonic :: (Eq r, Num r) => Map Var Var -> Multilinear r repr -> Multilinear r repr
renameMonotonic sub = M . Map.mapKeysMonotonic (Monomial . Set.map substVar . vars) . terms
  where substVar v = Map.findWithDefault v v sub

-- | Substitute a (Boolean) variable with a (Boolean) polynomial
subst :: (Eq r, Num r) => Var -> Multilinear FF2 'Mult -> Multilinear r 'Mult -> Multilinear r 'Mult
subst v p = substMany (Map.fromList [(v, p)])

-- | Simultaneous substitution of variables with polynomials
substMany :: (Eq r, Num r) =>
  Map Var (Multilinear FF2 'Mult) -> Multilinear r 'Mult -> Multilinear r 'Mult
substMany sub = normalize . Map.foldlWithKey' (\acc m a -> acc + substInMono m a) zero . terms
  where substInMono m a = distribute a $ foldl' (*) one (map substVar . Set.toList $ vars m)
        substVar v      = Map.findWithDefault (ofVar v) v sub

-- | Substitute a variable with a monomial
substMono :: (Eq r, Num r) => Var -> Monomial repr -> Multilinear r repr -> Multilinear r repr
substMono v m = M . Map.mapKeys  (Monomial . Set.foldl' substVar Set.empty . vars) . terms
  where substVar acc v'
          | v == v'   = Set.union acc $ vars m
          | otherwise = Set.insert v' acc

-- | Return a list of solutions to
--
-- > p = 0
--
--   Over a field
solveForX :: (Eq r, Fractional r, ReprC repr) => Multilinear r repr -> [(Var, Multilinear r repr)]
solveForX p = mapMaybe checkTerm . filter (\(_a,m) -> degree m == 1) $ toTermList p
  where checkTerm (a,m) =
          let v  = Set.elemAt 0 $ vars m
              p' = normalize $ p - ofTerm (a,m)
          in
            if not (contains v p')
            then Just (v, scale (recip a) p')
            else Nothing

{- Pseudo-boolean specific transformations -}

-- | Translate an additive monomial to a Boolean polynomial
polyOfXor :: Monomial 'Add -> Multilinear FF2 'Mult
polyOfXor = ofTermList . zip (repeat 1) . map (Monomial . Set.singleton) . Set.toList . vars

-- | Distribute a ring element over a monomial according to the equation
-- 
-- > axy = a/2x + a/2y - a/2(x + y)
--
unDistribute :: (Eq r, Num r, TwoRegular r) => r -> Monomial 'Mult -> Multilinear r 'Add
unDistribute a' = go a' . Set.toList . vars
  where go 0 _        = zero
        go a []       = one
        go a [x]      = ofTerm (a, Monomial $ Set.singleton x)
        go a (x:y:xs) =
          let recTerm = go (negate $ divTwo a) $ "-":xs
              sub     = Monomial $ Set.fromList [x, y]
          in
            go (divTwo a) (x:xs) + go (divTwo a) (y:xs) + substMono "-" sub recTerm

-- | Distribute a ring element over a Boolean polynomial according to the equation
-- 
-- > a(x + y) = ax + ay -2axy
--
distribute :: (Eq r, Num r) => r -> Multilinear FF2 'Mult -> Multilinear r 'Mult
distribute a = go a . Map.keys . terms
  where go 0 _      = zero
        go a []     = zero
        go a (m:xs) = ofTerm (a,m) + (go a xs) + (go (a * (-2)) $ map (m <>) xs)

-- | Perform the (pseudo-Boolean) Fourier transform
fourier :: (Eq r, Num r, TwoRegular r) => Multilinear r 'Mult -> Multilinear r 'Add
fourier = normalize . Map.foldlWithKey' addTerm zero . terms
  where addTerm acc m a = acc + unDistribute a m

-- | Perform the (pseudo-Boolean) inverse Fourier transform
invFourier :: (Eq r, Num r) => Multilinear r 'Add -> Multilinear r 'Mult
invFourier = normalize . Map.foldlWithKey' addTerm zero . terms
  where addTerm acc m a = acc + distribute a (polyOfXor m)

{- Constants, for testing -}

x0 = ofVar "x\x2080" :: Multilinear Double 'Mult
x1 = ofVar "x\x2081" :: Multilinear Double 'Mult
x2 = ofVar "x\x2082" :: Multilinear Double 'Mult
x3 = ofVar "x\x2083" :: Multilinear Double 'Mult
x4 = ofVar "x\x2084" :: Multilinear Double 'Mult
x5 = ofVar "x\x2085" :: Multilinear Double 'Mult
x6 = ofVar "x\x2086" :: Multilinear Double 'Mult
x7 = ofVar "x\x2087" :: Multilinear Double 'Mult
x8 = ofVar "x\x2088" :: Multilinear Double 'Mult
x9 = ofVar "x\x2089" :: Multilinear Double 'Mult

y0 = ofVar "y\x2080" :: Multilinear Double 'Add
y1 = ofVar "y\x2081" :: Multilinear Double 'Add
y2 = ofVar "y\x2082" :: Multilinear Double 'Add
y3 = ofVar "y\x2083" :: Multilinear Double 'Add
y4 = ofVar "y\x2084" :: Multilinear Double 'Add
y5 = ofVar "y\x2085" :: Multilinear Double 'Add
y6 = ofVar "y\x2086" :: Multilinear Double 'Add
y7 = ofVar "y\x2087" :: Multilinear Double 'Add
y8 = ofVar "y\x2088" :: Multilinear Double 'Add
y9 = ofVar "y\x2089" :: Multilinear Double 'Add
