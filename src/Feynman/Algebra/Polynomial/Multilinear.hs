{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

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
import Data.Map.Merge.Strict
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.Semigroup
import Data.Bits
import Data.String (IsString(..))

import Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial

{-----------------------------------
 Utility types
 -----------------------------------}

type Multilinear v r = Polynomial r (GrevlexML v)
type SBool v         = Polynomial FF2 (GrevlexML v)

instance Ring FF2
instance Field FF2

{-----------------------------------
 Multilinear Monomials
 -----------------------------------}

-- | Multilinear monomials with graded lexicographic (grevlex) order
newtype GrevlexML v = GrevlexML { unML :: Set v } deriving (Eq)

instance Ord v => Ord (GrevlexML v) where
  {-# INLINABLE compare #-}
  compare m n
    | k /= l    = compare k l
    | otherwise = case compare (unML n) (unML m) of
        EQ -> EQ
        LT -> GT
        GT -> LT
    where k = degree m
          l = degree n

instance Degree (GrevlexML v) where
  {-# INLINABLE degree #-}
  degree = Set.size . unML

instance Ord v => Vars (GrevlexML v) where
  type Var (GrevlexML v) = v
  {-# INLINABLE vars #-}
  vars = unML

instance Ord v => Semigroup (GrevlexML v) where
  {-# INLINABLE (<>) #-}
  m <> n = GrevlexML $ Set.union (unML m) (unML n)

instance Ord v => Monoid (GrevlexML v) where
  mempty = GrevlexML Set.empty

instance Ord v => Group (GrevlexML v) where
  m ./. n = GrevlexML $ Set.difference (unML m) (unML n)

instance Ord v => Symbolic (GrevlexML v) where
  ofVar v = GrevlexML $ Set.singleton v

instance Ord v => Monomial (GrevlexML v) where
  unMonomial = Set.toList . unML
  monomial   = GrevlexML . Set.fromList
  leastCM    = (<>)
  divides m  = (vars m `Set.isSubsetOf`) . vars

instance (Show v) => Show (GrevlexML v) where
  show = concatMap show . Set.toList . unML

-- | Multilinear monomials in the parity basis
newtype Parity v = Parity { unPar :: Set v } deriving (Eq)

instance Ord v => Ord (Parity v) where
  {-# INLINABLE compare #-}
  compare m n
    | k /= l    = compare k l
    | otherwise = case compare (unPar n) (unPar m) of
        EQ -> EQ
        LT -> GT
        GT -> LT
    where k = degree m
          l = degree n

instance Degree (Parity v) where
  {-# INLINABLE degree #-}
  degree = Set.size . unPar

instance Ord v => Vars (Parity v) where
  type Var (Parity v) = v
  {-# INLINABLE vars #-}
  vars = unPar

instance Ord v => Semigroup (Parity v) where
  {-# INLINABLE (<>) #-}
  m <> n =
    let symDiff a b = Set.difference (Set.union a b) (Set.intersection a b) in
      Parity $ symDiff (unPar m) (unPar n)

instance Ord v => Monoid (Parity v) where
  mempty = Parity Set.empty

instance Ord v => Group (Parity v) where
  (./.) = (<>)

instance Ord v => Symbolic (Parity v) where
  ofVar v = Parity $ Set.singleton v

instance Ord v => Monomial (Parity v) where
  unMonomial = Set.toList . unPar
  monomial   = Parity . Set.fromList
  leastCM    = (<>)
  divides m  = (vars m `Set.isSubsetOf`) . vars

instance (Show v) => Show (Parity v) where
  show = intercalate Unicode.oplus . map show . Set.toList . unPar

{-----------------------------------
 Methods specific to Boolean polynomials
 -----------------------------------}

-- | Factorize a multilinear polynomial into irreducibles. Algorithm due to
--   A. Shpilka & I. Volkovich, /On the Relation between Polynomial Identity
--   Testing and Finding Variable Disjoint Factors/
factorize :: (Ord v, Eq r, Abelian r, Ring r) => Multilinear v r -> [Multilinear v r]
factorize p =
  let (factors, p') = factorizeTrivial p in
    factors ++ go p'
  where dx x poly = subst x 0 poly + subst x 1 poly
        go poly = do
          x <- Set.toList $ vars poly
          let g      = (subst x 0 poly) * (dx x poly)
          let (o, s) = Set.partition (\y -> (dx y g) == 0) $ Set.delete x (vars poly)
          if Set.null o
            then return poly
            else go (substMany (\y -> if Set.member y o then 1 else ofVar y) poly) ++
                 go (substMany (\y -> if Set.member y (Set.insert x s) then 1 else ofVar y) poly)

-- | Distribute a ring element over a Boolean polynomial according to the equation
-- 
-- > a(x + y) = ax + ay -2axy
--
distribute :: (Ord v, Eq r, Abelian r, Ring r) => r -> SBool v -> Multilinear v r
distribute a' = go a' . Map.keys . getTerms . normalize
  where go 0 _      = zero
        go a []     = zero
        go a [m]    = ofTerm (a,m)
        go a (m:xs) = ofTerm (a,m) + (go a xs) + (go (power (-2) a) $ map (m <>) xs)

{- Substitutions -}

-- | Simultaneous substitution of variables with Boolean polynomials
substBool :: (Ord v, Eq r, Abelian r, Ring r) => (v -> SBool v) -> Multilinear v r -> Multilinear v r
substBool sub = normalize . Map.foldrWithKey (\m a -> (+ substInMono m a)) zero . getTerms
  where substInMono m a = distribute a $ foldr (*) one (map sub . Set.toList $ vars m)

{-
-- | Substitute a (Boolean, multiplicative) monomial with a (Boolean) polynomial
substMonomial :: (Ord v, Eq r, Abelian r) => [v] -> SBool v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
substMonomial xs p = normalize . Map.foldrWithKey (\m a acc -> addM acc $ substMonoInMono m a) zero . getTerms
  where m = Set.fromList xs
        substMonoInMono m' a
          | not (m `Set.isSubsetOf` (getVars m')) = ofTerm (a,m')
          | otherwise = distribute a $ p * ofMonomial (Monomial $ Set.difference (getVars m') m)

-- | Substitute a variable with a monomial
substVarMono :: (Ord v, Eq r, Num r, ReprC repr) =>
             v -> Monomial v repr -> Multilinear v r repr -> Multilinear v r repr
substVarMono v m = M . Map.mapKeys (Set.foldr substVar mempty . getVars) . getTerms
  where substVar v' acc
          | v == v'   = acc <> m
          | otherwise = acc <> monomial [v']

-- | Find a necessary substitution solving @p = 0@ over a field
solveForX :: (Ord v, Eq r, Fractional r, ReprC repr) =>
             Multilinear v r repr -> [(v, Multilinear v r repr)]
solveForX p = mapMaybe checkTerm . filter (\(_a,m) -> degree m == 1) $ toTermList p
  where checkTerm (a,m) =
          let v  = Set.elemAt 0 $ getVars m
              p' = p - ofTerm (a,m)
          in
            if not (contains v p')
            then Just (v, scale (recip a) p')
            else Nothing

-- | Return a list of solutions to @p = 0@ over a field
allSolutions :: (Ord v, Eq r, Fractional r, Abelian r) =>
             Multilinear v r 'Mult -> [(v, Multilinear v r 'Mult)]
allSolutions = concatMap solveForX . factorize

-- | Return a single solution to @p = 0@
getSolution :: (Ord v, Eq r, Fractional r, Abelian r) =>
             Multilinear v r 'Mult -> (v, Multilinear v r 'Mult)
getSolution = head . concatMap solveForX . factorize

{- Pseudo-boolean specific transformations -}

-- | Translate a monomial to a Boolean polynomial
liftImpl :: Ord v => ReprWit repr -> Monomial v repr -> SBool v
liftImpl WitMult = M . (flip Map.singleton) 1
liftImpl WitAdd  = ofTermList . zip (repeat 1) . Set.toList . Set.map f . getVars
  where f = Monomial . Set.singleton

-- | Translate an additive monomial to a Boolean polynomial
liftMonomial :: (Ord v, ReprC repr) => Monomial v repr -> SBool v
liftMonomial = liftImpl witRepr

-- | Translate a Boolean polynomial into any ring (in this case, Z-module)
lift :: (Ord v, Eq r, Abelian r) => SBool v -> Multilinear v r 'Mult
lift = distribute 1

-- | Distribute a ring element over a monomial according to the equation
-- 
-- > axy = a/2x + a/2y - a/2(x + y)
--
unDistribute :: (Ord v, Eq r, Num r, Dyadic r) => r -> Monomial v 'Mult -> Multilinear v r 'Add
unDistribute a' = go a' . Set.toList . getVars
  where go 0 _        = zero
        go a []       = constant a
        go a [x]      = ofTerm (a, Monomial $ Set.singleton x)
        go a (x:y:xs) =
          let recTerm = go (negate $ divTwo a) $ x:xs
              sub     = Monomial $ Set.fromList [x, y]
          in
            go (divTwo a) (x:xs) + go (divTwo a) (y:xs) + substVarMono x sub recTerm

-- | Non-recursive exclusion-inclusion formula
excInc :: (Ord v, Eq r, Dyadic r) => Monomial v 'Mult -> Multilinear v r 'Add
excInc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            fromDyadic $ dyadic (if n `mod` 2 == 0 then -1 else 1) (Set.size s - 1)

-- | Non-recursive inclusion-exclusion formula
incExc :: (Ord v, Eq r, Abelian r) => Monomial v 'Add -> Multilinear v r 'Mult
incExc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            if n `mod` 2 == 0 then power (-1 `shiftL` (n-1)) 1 else power (1 `shiftL` (n-1)) 1

-- | Perform the (pseudo-Boolean) Fourier transform
fourier :: (Ord v, Eq r, Dyadic r) => Multilinear v r 'Mult -> Multilinear v r 'Add
fourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ unDistribute a m

-- | Perform the (pseudo-Boolean) inverse Fourier transform
invFourier :: (Ord v, Eq r, Abelian r) => Multilinear v r 'Add -> Multilinear v r 'Mult
invFourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ distribute a (liftMonomial m)

-- | Canonicalize an additive multilinear polynomial
canonicalize :: (Ord v, Eq r, Dyadic r, Abelian r) => Multilinear v r 'Add -> Multilinear v r 'Add
canonicalize = fourier . invFourier

-- Constants, for testing

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

y0 = ofVar (IVar ("y",0)) :: Multilinear IVar DMod2 'Mult
y1 = ofVar (IVar ("y",1)) :: Multilinear IVar DMod2 'Mult
y2 = ofVar (IVar ("y",2)) :: Multilinear IVar DMod2 'Mult
y3 = ofVar (IVar ("y",3)) :: Multilinear IVar DMod2 'Mult
y4 = ofVar (IVar ("y",4)) :: Multilinear IVar DMod2 'Mult
y5 = ofVar (IVar ("y",5)) :: Multilinear IVar DMod2 'Mult
y6 = ofVar (IVar ("y",6)) :: Multilinear IVar DMod2 'Mult
y7 = ofVar (IVar ("y",7)) :: Multilinear IVar DMod2 'Mult
y8 = ofVar (IVar ("y",8)) :: Multilinear IVar DMod2 'Mult
y9 = ofVar (IVar ("y",9)) :: Multilinear IVar DMod2 'Mult
-}
