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

module Feynman.Algebra.Polynomial.Multilinear(
  Elim(..),
  Monomial(..),
  PowerProduct,
  Parity,
  Multilinear,
  PhasePolynomial,
  PseudoBoolean,
  SBool,
  lexOrd,
  grevlexOrd,
  lexdegOrd,
  monomial,
  coefficients,
  support,
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
  asVar,
  scale,
  divVar,
  quotVar,
  remVar,
  factorizeTrivial,
  factorize,
  dropConstant,
  cast,
  castMaybe,
  collectBy,
  collectVar,
  collectVars,
  rename,
  renameMonotonic,
  subst,
  substMany,
  substMonomial,
  solveForX,
  allSolutions,
  getSolution,
  liftMonomial,
  lift,
  distribute,
  excInc,
  incExc,
  fourier,
  invFourier,
  canonicalize
  ) where

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

-- | Class of elimination variables
class Ord v => Elim v where
  eliminate :: v -> Bool

{-----------------------------------
 Monomials
 -----------------------------------}

{- TODO: Comparing sets of variables is quite slow. Make the representation
         of monomials generic so that we can implement monomials with, e.g.,
         int sets for different variable classes -}

-- | Monomials with lexicographic order
newtype Monomial v (repr :: Repr) = Monomial { getVars :: Set v } deriving (Eq)

type PowerProduct v = Monomial v 'Mult
type Parity v       = Monomial v 'Add

-- | Lexicographic ordering
lexOrd :: Ord v => Monomial v repr -> Monomial v repr -> Ordering
lexOrd m n = compare (getVars m) (getVars n)

-- | Graded reverse lexicographic ordering
grevlexOrd :: Ord v => Monomial v repr -> Monomial v repr -> Ordering
grevlexOrd m n
    | k /= l    = compare k l
    | otherwise = compare (Set.toAscList $ getVars m) (Set.toAscList $ getVars n)
    where k = degree m
          l = degree n

-- | Elimination order with local grevlex
lexdegOrd :: Elim v => Monomial v repr -> Monomial v repr -> Ordering
lexdegOrd m n = case grevlexOrd (Monomial mx) (Monomial nx) of
  EQ -> grevlexOrd (Monomial my) (Monomial ny)
  or -> or
  where (mx, my) = Set.partition eliminate $ getVars m
        (nx, ny) = Set.partition eliminate $ getVars n

-- | Default instance of order monomials
instance Ord (Monomial String repr) where
  compare = grevlexOrd

instance Degree (Monomial v repr) where
  {-# INLINABLE degree #-}
  degree = Set.size . getVars

instance Ord v => Vars (Monomial v repr) where
  type Var (Monomial v repr) = v
  {-# INLINABLE vars #-}
  vars = getVars

showImpl :: Show v => ReprWit repr -> Monomial v repr -> String
showImpl WitAdd  = intercalate Unicode.oplus . map show . Set.toList . getVars
showImpl WitMult = concatMap show . Set.toList . getVars

instance (Show v, ReprC repr) => Show (Monomial v repr) where
  show = showImpl witRepr

mappendImpl :: Ord v => ReprWit repr -> Monomial v repr -> Monomial v repr -> Monomial v repr
mappendImpl WitMult m = Monomial . Set.union (getVars m) . getVars
mappendImpl WitAdd m  = Monomial . symDiff (getVars m) . getVars
  where symDiff a b = Set.difference (Set.union a b) (Set.intersection a b)

instance (Ord v, ReprC repr) => Semigroup (Monomial v repr) where
  (<>) = mappendImpl witRepr

instance (Ord v, ReprC repr) => Monoid (Monomial v repr) where
  mempty  = Monomial Set.empty
  mappend = (<>)

instance (Ord v) => Group (Monomial v 'Mult) where
  m ./. n = Monomial $ Set.difference (getVars m) (getVars n)

instance (Ord v, ReprC repr) => Symbolic (Monomial v repr) where
  ofVar v = Monomial $ Set.singleton v

-- | Construct a monomial
monomial :: Ord v => [v] -> Monomial v repr
monomial = Monomial . Set.fromList

{-----------------------------------
 Multilinear polynomials
 -----------------------------------}

-- | Multilinear polynomials over a ring 'r' with representation 'repr'
data Multilinear v r (repr :: Repr) = M { getTerms :: !(Map (Monomial v repr) r) }
  deriving (Eq)

-- | Convenience types
type PhasePolynomial v r  = Multilinear v r 'Add
type PseudoBoolean v r    = Multilinear v r 'Mult
type SBool v              = Multilinear v FF2 'Mult

instance (Ord r, Ord v, Ord (Monomial v repr)) => Ord (Multilinear v r repr) where
  compare p q = compare (getTerms p) (getTerms q)

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
  degree poly = case support poly of
    [] -> -1
    xs -> maximum . map degree $ xs

instance (Ord v) => Vars (Multilinear v r repr) where
  type Var (Multilinear v r repr) = v
  {-# INLINABLE vars #-}
  vars = foldr (Set.union) Set.empty . map getVars . Map.keys . getTerms

instance (Ord v, Eq r, Num r, ReprC repr) => Symbolic (Multilinear v r repr) where
  ofVar v = ofTerm (1, ofVar v)
  
instance (Ord v, Ord (Monomial v repr), Eq r, Num r, ReprC repr) => Num (Multilinear v r repr) where
  (+) = \p -> normalize . addM p
  (*) = \p -> normalize . multM witRepr p
  negate (M t) = M $ Map.map negate t
  abs    = id
  signum = id
  fromInteger 0 = M $ Map.empty
  fromInteger i = M . Map.singleton (Monomial Set.empty) $ fromInteger i

instance (Ord v, Ord (Monomial v repr), Eq r, Abelian r, ReprC repr) => Abelian (Multilinear v r repr) where
  power i = normalize . M . Map.map (power i) . getTerms

instance (Ord v, Ord (Monomial v repr), Eq r, Periodic r, ReprC repr) => Periodic (Multilinear v r repr) where
  order = Map.foldr (\a -> lcm (order a)) 1 . getTerms

instance (Ord v, IsString v, Eq r, Num r, ReprC repr) => IsString (Multilinear v r repr) where
  fromString s = ofVar (fromString s)

{- Accessors -}

-- | Get a list of the coefficients in grevlex order
coefficients :: Multilinear v r repr -> [r]
coefficients = Map.elems . getTerms

-- | Get the support in grevlex order
support :: Multilinear v r repr -> [Monomial v repr]
support = Map.keys . getTerms

-- | Get the terms in grevlex order
toTermList :: Multilinear v r repr -> [(r, Monomial v repr)]
toTermList = map swap . Map.toList . getTerms

-- | Retrieve the constant term
getConstant :: (Ord (Monomial v repr), Eq r, Num r) => Multilinear v r repr -> r
getConstant = Map.findWithDefault 0 (Monomial Set.empty) . getTerms

{- Tests -}

-- | Check if the polynomial is the zero function
isZero :: Multilinear v r repr -> Bool
isZero = Map.null . getTerms

-- | Check if the polynomial is a monomial
isMono :: Multilinear v r repr -> Bool
isMono = (1 >=) . Map.size . getTerms

-- | Check if the polynomial is constant
isConst :: Ord (Monomial v repr) => Multilinear v r repr -> Bool
isConst = (== [Monomial Set.empty]) . Map.keys . getTerms

-- | Check if a variable is used in the polynomial
contains :: Ord v => v -> Multilinear v r repr -> Bool
contains v = any (Set.member v . getVars) . Map.keys . getTerms

{- Special forms -}

-- | Check if the polynomial is of the form /v/ for some variable /v/
asVar :: (Eq r, Num r) => Multilinear v r repr -> Maybe v
asVar p = case map (Set.toList . getVars . snd) . filter ((1 ==) . fst) $ toTermList p of
  ([v]):[]  -> Just v
  otherwise -> Nothing

{- Constructors -}

-- | Constant polynomial
constant :: (Ord (Monomial v repr), Eq r, Num r, ReprC repr) => r -> Multilinear v r repr
constant 0 = M $ Map.empty
constant a = M $ Map.singleton (Monomial Set.empty) a

-- | Construct the polynomial /m/ for a monomial /m/
ofMonomial :: (Ord v, Eq r, Num r, ReprC repr) => Monomial v repr -> Multilinear v r repr
ofMonomial m = ofTerm (1, m)

-- | Construct the polynomial /a*m/
ofTerm :: (Ord v, Eq r, Num r, ReprC repr) => (r, Monomial v repr) -> Multilinear v r repr
ofTerm (0, _) = M $ Map.empty
ofTerm (a, m) = M $ Map.singleton m a

-- | Construct the polynomial /a*m/
ofTermList :: (Ord (Monomial v repr), Eq r, Num r, ReprC repr) => [(r, Monomial v repr)] -> Multilinear v r repr
ofTermList = M . Map.fromList . filter ((/= 0) . snd) . map swap

{- Arithmetic -}

-- | Scale a 
scale :: (Ord v, Ord (Monomial v repr), Eq r, Num r, ReprC repr) => r -> Multilinear v r repr -> Multilinear v r repr
scale a
  | a == 0    = \_ -> 0
  | otherwise = M . Map.map (a*) . getTerms

-- | Add two polynomials with the same representation
addM :: (Ord (Monomial v repr), Eq r, Num r, ReprC repr) =>
        Multilinear v r repr -> Multilinear v r repr -> Multilinear v r repr
addM p = M . Map.unionWith (+) (getTerms p) . getTerms
{-
addM p q = M $ unionN (getTerms p) (getTerms q) where
  unionN = merge preserveMissing preserveMissing (zipWithMaybeMatched f)
  f m a1 a2 = case (a1 + a2) of
    0  -> Nothing
    a3 -> Just a3
-}

-- | Multiply two polynomials with the same representation
multM :: (Ord v, Ord (Monomial v repr), Eq r, Num r) =>
         ReprWit repr -> Multilinear v r repr -> Multilinear v r repr -> Multilinear v r repr
multM wit p q = case wit of
  WitAdd  -> error "Error: multiplying additive phase polynomials"
  WitMult -> multImpl p q

-- Note on implementation: with a monomial order we wouldn't need the
-- intermediate sorting step, but multilinear monomials appear to
-- hence no valid monomial order over <>. This version maintains
-- some efficiency since most of the time the terms will already
-- be sorted. Can drop it when we do have a monomial order.
multImpl :: (Ord v, Ord (Monomial v 'Mult), Eq r, Num r) =>
            Multilinear v r 'Mult -> Multilinear v r 'Mult -> Multilinear v r 'Mult
multImpl p
  | p == 0           = \_ -> 0
  | otherwise        = Map.foldrWithKey (\m a acc -> addM acc $ multTerm m a) zero . getTerms
  where multTerm m a = M . Map.fromAscList . process m a . Map.toAscList $ tms
        process m a  = sumUp . groupMono . sortMono . multBy m a
        multBy m a   = map $ \(m',a') -> (m<>m', a*a')
        sortMono     = sortBy $ \(m,a) (m',a') -> compare m m'
        groupMono    = groupBy (\t t' -> fst t == fst t')
        sumUp        = map $ foldr1 (\(m,a) (_,a') -> (m,a+a'))
        tms          = getTerms p

-- | Performs the Euclidean division of a polynomial 'p' by a variables 'x', such that
--
--   @ p = 'ofVar' x * 'fst' ('varDiv' p x) + 'snd' ('varDiv' p x) @
divVar :: (Ord v, Ord (Monomial v 'Mult)) => Multilinear v r 'Mult -> v -> (Multilinear v r 'Mult, Multilinear v r 'Mult)
divVar p x = (M $ Map.mapKeys (Monomial . Set.delete x . getVars) qTerms, M rTerms)
  where (qTerms, rTerms) = Map.partitionWithKey f $ getTerms p
        f m _a           = Set.member x $ getVars m

-- | Takes the quotient of 'p'/'x'
quotVar :: (Ord v, Ord (Monomial v 'Mult)) => v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
quotVar x = M . Map.mapKeys (Monomial . Set.delete x . getVars) . takeQuotient . getTerms
  where takeQuotient = Map.filterWithKey (\m _a -> Set.member x $ getVars m)

-- | Takes the remainder of 'p'/'x'
remVar :: (Ord v, Ord (Monomial v 'Mult)) => v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
remVar x = M . Map.filterWithKey (\m _a -> not $ Set.member x $ getVars m) . getTerms

-- | Factors out all trivial factors
factorizeTrivial :: (Ord v, Ord (Monomial v 'Mult), Eq r, Num r) =>
                    Multilinear v r 'Mult -> ([Multilinear v r 'Mult], Multilinear v r 'Mult)
factorizeTrivial p = Set.foldr tryDiv ([], p) $ vars p
  where tryDiv x  (acc, poly) =
          let (q, r) = divVar poly x in
            if isZero r then ((ofVar x):acc, q) else (acc, poly)

-- | Factorize a multilinear polynomial into irreducibles. Algorithm due to
--   A. Shpilka & I. Volkovich, /On the Relation between Polynomial Identity
--   Testing and Finding Variable Disjoint Factors/
factorize :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => Multilinear v r 'Mult -> [Multilinear v r 'Mult]
factorize p =
  let (factors, p') = factorizeTrivial p in
    factors ++ [p'] -- go p'
  where dx x poly = subst x 0 poly + subst x 1 poly
        go poly = do
          x <- Set.toList $ vars poly
          let g      = (subst x 0 poly) * (dx x poly)
          let (o, s) = Set.partition (\y -> (dx y g) == 0) $ Set.delete x (vars poly)
          if Set.null o
            then return poly
            else go (substMany (\y -> if Set.member y o then 1 else ofVar y) poly) ++
                 go (substMany (\y -> if Set.member y (Set.insert x s) then 1 else ofVar y) poly)

{- Transformations -}

-- | Normalize a multilinear polynomial
normalize :: (Ord (Monomial v repr), Eq r, Num r) => Multilinear v r repr -> Multilinear v r repr
normalize = M . Map.filter (0/=) . getTerms

-- | Drops the constant term. Useful for verification up to global phase
dropConstant :: (Ord (Monomial v repr), Eq r, Num r) => Multilinear v r repr -> Multilinear v r repr
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
collectVar :: (Ord v, Ord (Monomial v repr)) => v -> Multilinear v r repr -> Multilinear v r repr
collectVar v = collectBy (\(_a, m) -> Set.member v $ getVars m)

-- | Collects the terms of a polynomial containing a set of variables
collectVars :: (Ord v, Ord (Monomial v repr)) => Set v -> Multilinear v r repr -> Multilinear v r repr
collectVars s = collectBy (\(_a, m) -> (getVars m) `Set.isSubsetOf` s)

{- Substitutions -}

-- | Rename variables according to a variable map
rename :: (Ord v', Ord (Monomial v repr), Ord (Monomial v' repr)) => (v -> v') -> Multilinear v r repr -> Multilinear v' r repr
rename sub = M . Map.mapKeys (Monomial . Set.map sub . getVars) . getTerms

-- | Rename variables according to a monotonic variable map
renameMonotonic :: (Ord v', Ord (Monomial v repr)) => (v -> v') -> Multilinear v r repr -> Multilinear v' r repr
renameMonotonic sub = M . Map.mapKeysMonotonic (Monomial . Set.map sub . getVars) . getTerms

-- | Substitute a (Boolean) variable with a (Boolean) polynomial
subst :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => v -> SBool v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
subst v p = substMany (\v' -> if v' == v then p else ofVar v')

-- | Simultaneous substitution of variables with polynomials
substMany :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => (v -> SBool v) -> Multilinear v r 'Mult -> Multilinear v r 'Mult
substMany sub = normalize . Map.foldrWithKey (\m a acc -> addM acc $ substInMono m a) zero . getTerms
  where substInMono m a = distribute a $ foldr (multImpl) one (map sub . Set.toList $ getVars m)

-- | Substitute a (Boolean, multiplicative) monomial with a (Boolean) polynomial
substMonomial :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => [v] -> SBool v -> Multilinear v r 'Mult -> Multilinear v r 'Mult
substMonomial xs p = normalize . Map.foldrWithKey (\m a acc -> addM acc $ substMonoInMono m a) zero . getTerms
  where m = Set.fromList xs
        substMonoInMono m' a
          | not (m `Set.isSubsetOf` (getVars m')) = ofTerm (a,m')
          | otherwise = distribute a $ p * ofMonomial (Monomial $ Set.difference (getVars m') m)

-- | Substitute a variable with a monomial
substVarMono :: (Ord v, Ord (Monomial v repr), Eq r, Num r, ReprC repr) =>
             v -> Monomial v repr -> Multilinear v r repr -> Multilinear v r repr
substVarMono v m = M . Map.mapKeys (Set.foldr substVar mempty . getVars) . getTerms
  where substVar v' acc
          | v == v'   = acc <> m
          | otherwise = acc <> monomial [v']

-- | Find a necessary substitution solving @p = 0@ over a field
solveForX :: (Ord v, Ord (Monomial v repr), Eq r, Fractional r, ReprC repr) =>
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
allSolutions :: (Ord v, Ord (Monomial v 'Mult), Eq r, Fractional r, Abelian r) =>
             Multilinear v r 'Mult -> [(v, Multilinear v r 'Mult)]
allSolutions = concatMap solveForX . factorize

-- | Return a single solution to @p = 0@
getSolution :: (Ord v, Ord (Monomial v 'Mult), Eq r, Fractional r, Abelian r) =>
             Multilinear v r 'Mult -> (v, Multilinear v r 'Mult)
getSolution = head . concatMap solveForX . factorize

{- Pseudo-boolean specific transformations -}

-- | Translate a monomial to a Boolean polynomial
liftImpl :: (Ord (Monomial v repr), Ord (Monomial v 'Mult)) => ReprWit repr -> Monomial v repr -> SBool v
liftImpl WitMult = M . (flip Map.singleton) 1
liftImpl WitAdd  = ofTermList . zip (repeat 1) . Set.toList . Set.map f . getVars
  where f = Monomial . Set.singleton

-- | Translate an additive monomial to a Boolean polynomial
liftMonomial :: (Ord (Monomial v repr), Ord (Monomial v 'Mult), ReprC repr) => Monomial v repr -> SBool v
liftMonomial = liftImpl witRepr

-- | Translate a Boolean polynomial into any ring (in this case, Z-module)
lift :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => SBool v -> Multilinear v r 'Mult
lift = distribute 1

-- | Distribute a ring element over a monomial according to the equation
-- 
-- > axy = a/2x + a/2y - a/2(x + y)
--
unDistribute :: (Ord v, Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Num r, Dyadic r) => r -> Monomial v 'Mult -> Multilinear v r 'Add
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
excInc :: (Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Dyadic r) => Monomial v 'Mult -> Multilinear v r 'Add
excInc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            fromDyadic $ dyadic (if n `mod` 2 == 0 then -1 else 1) (Set.size s - 1)

-- | Distribute a ring element over a Boolean polynomial according to the equation
-- 
-- > a(x + y) = ax + ay -2axy
--
distribute :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => r -> SBool v -> Multilinear v r 'Mult
distribute a' = go a' . Map.keys . getTerms . normalize
  where go 0 _      = zero
        go a []     = zero
        go a [m]    = ofTerm (a,m)
        go a (m:xs) = ofTerm (a,m) + (go a xs) + (go (power (-2) a) $ map (m <>) xs)

-- | Non-recursive inclusion-exclusion formula
incExc :: (Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Abelian r) => Monomial v 'Add -> Multilinear v r 'Mult
incExc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            if n `mod` 2 == 0 then power (-1 `shiftL` (n-1)) 1 else power (1 `shiftL` (n-1)) 1

-- | Perform the (pseudo-Boolean) Fourier transform
fourier :: (Ord v, Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Dyadic r) => Multilinear v r 'Mult -> Multilinear v r 'Add
fourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ unDistribute a m

-- | Perform the (pseudo-Boolean) inverse Fourier transform
invFourier :: (Ord v, Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Abelian r) => Multilinear v r 'Add -> Multilinear v r 'Mult
invFourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ distribute a (liftMonomial m)

-- | Canonicalize an additive multilinear polynomial
canonicalize :: (Ord v, Ord (Monomial v 'Mult), Ord (Monomial v 'Add), Eq r, Dyadic r, Abelian r) => Multilinear v r 'Add -> Multilinear v r 'Add
canonicalize = fourier . invFourier

-- Constants, for testing

newtype IVar = IVar (String, Integer) deriving (Eq, Ord)

instance Elim IVar where
  eliminate (IVar (a,_)) = a == "t"

instance Ord (Monomial IVar repr) where
  compare = lexdegOrd

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

powerSet :: [a] -> [[a]]
powerSet []     = [[]]
powerSet (x:xs) = [x:ps | ps <- powerSet xs] ++ powerSet xs

allPolynomials :: (Ord v, Ord (Monomial v 'Mult), Eq r, Abelian r) => [Multilinear v r 'Mult] -> [Multilinear v r 'Mult]
allPolynomials = polynomials . monomials where
  monomials = map (foldr (*) 1) . powerSet
  polynomials = map (foldr (+) 0) . powerSet

{-
--x1, x2, x3, y1, y2, y3 :: Multivariate IVar FF2
x1,x2,x3,y1,y2,y3 :: IVar
x1 = IVar ("x",1)
x2 = IVar ("x",2)
x3 = IVar ("x",3)
y1 = IVar ("t",1)
y2 = IVar ("t",2)
y3 = IVar ("t",3)

combinations :: [a] -> [[a]]
combinations []     = [[]]
combinations (x:xs) = combinations xs ++ (map (x:) $ combinations xs)

varOrd1 :: [Monomial IVar 'Mult]
varOrd1 = reverse $ sort $ map monomial $ combinations [x1,x2,x3]

varOrd2 :: [Monomial IVar 'Mult]
varOrd2 = reverse $ sort $ map monomial $ combinations [x1,x2,x3,y1,y2,y3]

varOrd3 :: [Monomial IVar 'Mult]
varOrd3 = reverse $ sort $ map monomial $ [[x1,x1],[x1,x2],[x1,x3],[x2,x2],[x2,x3],[x3,x3]]

varOrd4 :: [Monomial IVar 'Mult]
varOrd4 = reverse $ sort $ map monomial $ [[x1,x1],[x1,x2],[x1,x3],[x2,x2],[x2,x3],[x3,x3]]

varOrd5 :: [Monomial IVar 'Mult]
varOrd5 = reverse $ sort $ map monomial $ [[y1,x1],[x1,y2],[x1,x3],[y2,y2],[x2,y3],[x3,x3]]
-}
