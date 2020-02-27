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

module Feynman.Algebra.Polynomial.Multilinear(
  Monomial,
  Multilinear,
  PhasePoly,
  PseudoBool,
  BoolPoly,
  coefficients,
  toTermList,
  vars,
  getConstant,
  isZero,
  isMono,
  isConst,
  contains,
  constant,
  ofVar,
  ofMonomial,
  ofTerm,
  ofTermList,
  ofTermDirect,
  scale,
  factorVar,
  divVar,
  remVar,
  dropConstant,
  cast,
  castMaybe,
  collectBy,
  collectVar,
  rename,
  renameMonotonic,
  gets,
  substMany,
  solveForX,
  polyOfXor,
  fourier,
  invFourier,
  canonicalize
  ) where

import Data.Kind
import Data.Tuple
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Semigroup

import Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial

{-----------------------------------
 Utility types
 -----------------------------------}

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

-- | Monomials with graded lexicographic (grevlex) order
newtype Monomial v (repr :: Repr) = Monomial { getVars :: Set v } deriving (Eq)

instance Ord v => Ord (Monomial v repr) where
  compare m n = case compare (degree m) (degree n) of
    EQ -> compare (getVars m) (getVars n)
    x  -> x

instance Degree (Monomial v repr) where
  degree = Set.size . getVars

showMonomial :: Show v => ReprWit repr -> Monomial v repr -> String
showMonomial wit = case wit of
  WitAdd  -> intercalate Unicode.oplus . map show . Set.toList . getVars
  WitMult -> concatMap show . Set.toList . getVars

instance (Show v, ReprC repr) => Show (Monomial v repr) where
  show = showMonomial witRepr

instance Ord v => Semigroup (Monomial v 'Mult) where
  m <> m' = Monomial $ Set.union (getVars m) (getVars m')

instance Ord v => Monoid (Monomial v 'Mult) where
  mempty  = Monomial Set.empty
  mappend = (<>)

{-----------------------------------
 Multilinear polynomials
 -----------------------------------}

-- | Multilinear polynomials over a ring 'r' with representation 'repr'
data Multilinear v r (repr :: Repr) = M { getTerms :: !(Map (Monomial v repr) r) }
  deriving (Eq, Ord)

-- | Convenience types
type PhasePoly v r  = Multilinear v r 'Add
type PseudoBool v r = Multilinear v r 'Mult
type BoolPoly v     = Multilinear v FF2 'Mult

instance (Show v, Eq r, Num r, Show r, ReprC repr) => Show (Multilinear v r repr) where
  show p@(M t)
    | isZero p  = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs t)
    where showTerm (mono, coeff)
            | degree mono == 0 = show coeff
            | coeff == 1       = show mono
            | coeff == -1      = "-" ++ show mono
            | otherwise        = show coeff ++ show mono

instance Degree (Multilinear v r repr) where
  degree (M t) = case Map.lookupMax t of
    Nothing      -> -1
    Just (m, _a) -> degree m

instance (Ord v, Eq r, Num r, ReprC repr) => Num (Multilinear v r repr) where
  (+) = addM
  (*) = multM witRepr
  negate (M t) = M $ Map.map negate t
  abs    p = p
  signum p = p
  fromInteger 0 = M $ Map.empty
  fromInteger i = M . Map.singleton (Monomial Set.empty) $ fromInteger i

{- Accessors -}

-- | Get a list of the coefficients in grevlex order
coefficients :: Multilinear v r repr -> [r]
coefficients = Map.elems . getTerms

-- | Get the terms in grevlex order
toTermList :: Multilinear v r repr -> [(r, Monomial v repr)]
toTermList = map swap . Map.toList . getTerms

-- | Get a list of variables contained in the polynomial
vars :: Ord v => Multilinear v r repr -> Set v
vars = foldr (Set.union) Set.empty . map getVars . Map.keys . getTerms

-- | Retrieve the constant term
getConstant :: (Ord v, Eq r, Num r) => Multilinear v r repr -> r
getConstant = Map.findWithDefault 0 (Monomial Set.empty) . getTerms

{- Tests -}

-- | Check if the polynomial is the zero function
isZero :: Multilinear v r repr -> Bool
isZero = Map.null . getTerms

-- | Check if the polynomial is a monomial
isMono :: Multilinear v r repr -> Bool
isMono = (1 >=) . Map.size . getTerms

-- | Check if the polynomial is constant
isConst :: Ord v => Multilinear v r repr -> Bool
isConst = (== [Monomial Set.empty]) . Map.keys . getTerms

-- | Check if a variable is used in the polynomial
contains :: Ord v => v -> Multilinear v r repr -> Bool
contains v = any (Set.member v . getVars) . Map.keys . getTerms

{- Constructors -}

-- | Constant polynomial
constant :: (Eq r, Num r) => r -> Multilinear v r repr
constant = normalize . M . Map.singleton (Monomial Set.empty)

-- | Construct the variable polynomial /x/
ofVar :: (Eq r, Num r) => v -> Multilinear v r repr
ofVar x = ofTerm (1, Monomial $ Set.singleton x)

-- | Construct the polynomial /m/ for a monomial /m/
ofMonomial :: (Eq r, Num r) => Monomial v repr -> Multilinear v r repr
ofMonomial m = ofTerm (1, m)

-- | Construct the polynomial /a*m/
ofTerm :: (Eq r, Num r) => (r, Monomial v repr) -> Multilinear v r repr
ofTerm (a, m) = normalize . M $ Map.singleton m a

-- | Construct the polynomial /a*m/
ofTermList :: (Ord v, Eq r, Num r) => [(r, Monomial v repr)] -> Multilinear v r repr
ofTermList = normalize . M . Map.fromList . map swap

-- | (Internal use only) Construct the polynomial /a*m/
ofTermDirect :: (Eq r, Num r) => (r, Monomial v repr) -> Multilinear v r repr
ofTermDirect (a, m) = M $ Map.singleton m a

{- Arithmetic -}

-- | Scale a 
scale :: (Ord v, Eq r, Num r, ReprC repr) => r -> Multilinear v r repr -> Multilinear v r repr
scale a p
  | a == 0    = zero
  | otherwise = M $ Map.map (a*) $ getTerms p

-- | Add two polynomials with the same representation
addM :: (Ord v, Eq r, Num r) =>
  Multilinear v r repr -> Multilinear v r repr -> Multilinear v r repr
addM p q = normalize . M $ Map.unionWith (+) (getTerms p) (getTerms q)

-- | Multiply two polynomials with the same representation
multM :: (Ord v, Eq r, Num r) =>
  ReprWit repr -> Multilinear v r repr -> Multilinear v r repr -> Multilinear v r repr
multM wit p q = case wit of
  WitAdd  -> error "Error: multiplying additive phase polynomials"
  WitMult -> normalize $ multImpl p q

multImpl :: (Ord v, Eq r, Num r) =>
  Multilinear v r 'Mult -> Multilinear v r 'Mult -> Multilinear v r 'Mult
multImpl p q = Map.foldlWithKey' multPolyTerm zero (getTerms p)
  where multPolyTerm acc m a =
          addM acc (M $ Map.foldlWithKey' (multTermTerm m a) Map.empty (getTerms q))
        multTermTerm m a acc m' a' = Map.alter (addCoeff $ a * a') (m <> m') acc
        addCoeff a b = case b of
          Nothing -> Just a
          Just c  -> Just $ a + c

-- | Factorizes a polynomial /p/ as /vq + r/
factorVar :: Ord v =>
  v -> Multilinear v r 'Mult -> (Multilinear v r 'Mult, Multilinear v r 'Mult)
factorVar v p = (M qTerms, M rTerms)
  where (qTerms, rTerms) = Map.partitionWithKey f $ getTerms p
        f m _a           = Set.member v $ getVars m

-- | Takes the quotient of /p\/v/
divVar :: Ord v => v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
divVar v = M . Map.mapKeys (Monomial . Set.delete v . getVars) . takeQuotient . getTerms
  where takeQuotient = Map.filterWithKey (\m _a -> Set.member v $ getVars m)

-- | Takes the quotient of /p\/v/
remVar :: Ord v => v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
remVar v = M . Map.filterWithKey (\m _a -> not $ Set.member v $ getVars m) . getTerms

{- Transformations -}

-- | Normalize a multilinear polynomial
normalize :: (Eq r, Num r) => Multilinear v r repr -> Multilinear v r repr
normalize = M . Map.filter (0/=) . getTerms

-- | Drops the constant term. Useful for verification up to global phase
dropConstant :: (Ord v, Eq r, Num r) => Multilinear v r repr -> Multilinear v r repr
dropConstant = M . (Map.delete (Monomial Set.empty) . getTerms)

-- | Cast a polynomial over ring /r/ to ring /s/
cast :: (r -> s) -> Multilinear v r repr -> Multilinear v s repr
cast f = M . Map.map f . getTerms

-- | Attempt to cast a polynomial over ring /r/ to ring /s/ via a partial function
castMaybe :: (r -> Maybe s) -> Multilinear v r repr -> Maybe (Multilinear v s repr)
castMaybe f = fmap M . mapM f . getTerms

-- | Collects just the terms of the polynomial satisfying a predicate
collectBy :: ((r, Monomial v repr) -> Bool) -> Multilinear v r repr -> Multilinear v r repr
collectBy f = M . Map.filterWithKey (curry $ f . swap) . getTerms

-- | Collects the terms of a polynomial containing a particular variable
collectVar :: Ord v => v -> Multilinear v r repr -> Multilinear v r repr
collectVar v = collectBy (\(_a, m) -> Set.member v $ getVars m)
  
{- Substitutions -}

-- | Rename variables according to a variable map
rename :: Ord v => (v -> v) -> Multilinear v r repr -> Multilinear v r repr
rename sub = M . Map.mapKeys (Monomial . Set.map sub . getVars) . getTerms

-- | Rename variables according to a monotonic variable map
renameMonotonic :: Ord v => (v -> v) -> Multilinear v r repr -> Multilinear v r repr
renameMonotonic sub = M . Map.mapKeysMonotonic (Monomial . Set.map sub . getVars) . getTerms

-- | Substitute a (Boolean) variable with a (Boolean) polynomial
gets :: (Ord v, Eq r, ZModule r) => v -> BoolPoly v -> PseudoBool v r -> PseudoBool v r
v `gets` p = substMany (\v' -> if v' == v then p else ofVar v)

-- | Simultaneous substitution of variables with polynomials
substMany :: (Ord v, Eq r, ZModule r) => (v -> BoolPoly v) -> PseudoBool v r -> PseudoBool v r
substMany sub = normalize . Map.foldlWithKey' (\acc m a -> acc + substInMono m a) zero . getTerms
  where substInMono m a = distribute a $ foldl' (*) one (map sub . Set.toList $ getVars m)

-- | Substitute a variable with a monomial
substMono :: (Ord v, Eq r, Num r) =>
  v -> Monomial v repr -> Multilinear v r repr -> Multilinear v r repr
substMono v m = M . Map.mapKeys  (Monomial . Set.foldl' substVar Set.empty . getVars) . getTerms
  where substVar acc v'
          | v == v'   = Set.union acc $ getVars m
          | otherwise = Set.insert v' acc

-- | Return a list of solutions to
--
--   @p = 0@
--
--   Over a field
solveForX :: (Ord v, Eq r, Fractional r, ReprC repr) =>
  Multilinear v r repr -> [(v, Multilinear v r repr)]
solveForX p = mapMaybe checkTerm . filter (\(_a,m) -> degree m == 1) $ toTermList p
  where checkTerm (a,m) =
          let v  = Set.elemAt 0 $ getVars m
              p' = normalize $ p - ofTerm (a,m)
          in
            if not (contains v p')
            then Just (v, scale (recip a) p')
            else Nothing

{- Pseudo-boolean specific transformations -}

-- | Translate an additive monomial to a Boolean polynomial
polyOfXor :: Ord v => Monomial v 'Add -> BoolPoly v
polyOfXor = ofTermList . zip (repeat 1) . map (Monomial . Set.singleton) . Set.toList . getVars

-- | Distribute a ring element over a monomial according to the equation
-- 
-- > axy = a/2x + a/2y - a/2(x + y)
--
unDistribute :: (Ord v, Eq r, Num r, TwoRegular r) => r -> Monomial v 'Mult -> PhasePoly v r
unDistribute a' = go a' . Set.toList . getVars
  where go 0 _        = zero
        go a []       = one
        go a [x]      = ofTerm (a, Monomial $ Set.singleton x)
        go a (x:y:xs) =
          let recTerm = go (negate $ divTwo a) $ x:xs
              sub     = Monomial $ Set.fromList [x, y]
          in
            go (divTwo a) (x:xs) + go (divTwo a) (y:xs) + substMono x sub recTerm

-- | Distribute a ring element over a Boolean polynomial according to the equation
-- 
-- > a(x + y) = ax + ay -2axy
--
distribute :: (Ord v, Eq r, ZModule r) => r -> BoolPoly v -> PseudoBool v r
distribute a' = go a' . Map.keys . getTerms
  where go 0 _      = zero
        go a []     = zero
        go a (m:xs) = ofTerm (a,m) + (go a xs) + (go (power (-2) a) $ map (m <>) xs)

-- | Perform the (pseudo-Boolean) Fourier transform
fourier :: (Ord v, Eq r, Num r, TwoRegular r) => PseudoBool v r -> PhasePoly v r
fourier = normalize . Map.foldlWithKey' addTerm zero . getTerms
  where addTerm acc m a = acc + unDistribute a m

-- | Perform the (pseudo-Boolean) inverse Fourier transform
invFourier :: (Ord v, Eq r, ZModule r) => PhasePoly v r -> PseudoBool v r
invFourier = normalize . Map.foldlWithKey' addTerm zero . getTerms
  where addTerm acc m a = acc + distribute a (polyOfXor m)

-- | Canonicalize an additive multilinear polynomial
canonicalize :: (Ord v, Eq r, TwoRegular r, ZModule r) => PhasePoly v r -> PhasePoly v r
canonicalize = fourier . invFourier

{- Constants, for testing -}

newtype IVar = IVar (String, Integer) deriving (Eq, Ord)

instance Show IVar where
  show (IVar (x, i)) = Unicode.sub x i

x0 = ofVar (IVar ("x",0)) :: Multilinear IVar DyadicRational 'Mult
x1 = ofVar (IVar ("x",1)) :: Multilinear IVar DyadicRational 'Mult
x2 = ofVar (IVar ("x",2)) :: Multilinear IVar DyadicRational 'Mult
x3 = ofVar (IVar ("x",3)) :: Multilinear IVar DyadicRational 'Mult
x4 = ofVar (IVar ("x",4)) :: Multilinear IVar DyadicRational 'Mult
x5 = ofVar (IVar ("x",5)) :: Multilinear IVar DyadicRational 'Mult
x6 = ofVar (IVar ("x",6)) :: Multilinear IVar DyadicRational 'Mult
x7 = ofVar (IVar ("x",7)) :: Multilinear IVar DyadicRational 'Mult
x8 = ofVar (IVar ("x",8)) :: Multilinear IVar DyadicRational 'Mult
x9 = ofVar (IVar ("x",9)) :: Multilinear IVar DyadicRational 'Mult

y0 = ofVar (IVar ("y",0)) :: Multilinear IVar DyadicRational 'Add
y1 = ofVar (IVar ("y",1)) :: Multilinear IVar DyadicRational 'Add
y2 = ofVar (IVar ("y",2)) :: Multilinear IVar DyadicRational 'Add
y3 = ofVar (IVar ("y",3)) :: Multilinear IVar DyadicRational 'Add
y4 = ofVar (IVar ("y",4)) :: Multilinear IVar DyadicRational 'Add
y5 = ofVar (IVar ("y",5)) :: Multilinear IVar DyadicRational 'Add
y6 = ofVar (IVar ("y",6)) :: Multilinear IVar DyadicRational 'Add
y7 = ofVar (IVar ("y",7)) :: Multilinear IVar DyadicRational 'Add
y8 = ofVar (IVar ("y",8)) :: Multilinear IVar DyadicRational 'Add
y9 = ofVar (IVar ("y",9)) :: Multilinear IVar DyadicRational 'Add

y1234 :: Multilinear IVar DMod2 'Add
y1234 = ofTerm (dMod2 1 2, Monomial $ Set.fromList xs)
  where xs = [IVar ("y", 1), IVar ("y", 2), IVar ("y", 3), IVar ("y", 4)]
