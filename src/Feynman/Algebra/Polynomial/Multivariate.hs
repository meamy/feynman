{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExplicitForAll #-}

{-|
Module      : Multivariate
Description : Multivariate polynomials
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Multivariate where

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
 Monomials
 -----------------------------------}

-- | Basic type of multivariate monomials
newtype Monomial ord v = Monomial { unM :: Map v Int }

instance Eq v => Eq (Monomial ord v) where
  {-# INLINABLE (==) #-}
  m == n = (Map.filter (/= 0) $ unM m) == (Map.filter (/= 0) $ unM n)

instance Degree (Monomial ord v) where
  {-# INLINABLE degree #-}
  degree = Map.foldl' (+) 0 . unM

instance Ord v => Vars (Monomial ord v) where
  type Var (Monomial ord v) = v
  {-# INLINABLE vars #-}
  vars = Set.fromList . Map.keys . unM

instance Ord v => Semigroup (Monomial ord v) where
  {-# INLINABLE (<>) #-}
  m <> n = Monomial $ Map.unionWith (+) (unM m) (unM n)

instance Ord v => Monoid (Monomial ord v) where
  mempty = Monomial Map.empty

instance Ord v => Group (Monomial ord v) where
  m ./. n = Monomial $ Map.unionWith (+) (unM m) (Map.map (negate) $ unM n)

instance Ord v => Symbolic (Monomial ord v) where
  ofVar v = Monomial $ Map.singleton v 1

instance (Show v) => Show (Monomial ord v) where
  show = concatMap showVar . Map.toList . Map.filter (/= 0) . unM where
    showVar (v,1) = show v
    showVar (v,i) = Unicode.sup (show v) (toInteger i)

{-----------------------------------
 Operations on Monomials
 -----------------------------------}

-- | Constructs a monomial from a multiset of variables
monomial :: Ord v => [v] -> Monomial ord v
monomial = foldr (\a -> ((ofVar a) <>)) mempty

-- | Deconstructs a monomial into a multiset of variables
unMonomial :: Monomial ord v -> [v]
unMonomial m = concat [replicate i a | (a,i) <- Map.toList $ unM m]

-- | Gives the least common multiple of two monomials
monomialLCM :: Ord v => Monomial ord v -> Monomial ord v -> Monomial ord v
monomialLCM m n = Monomial $ Map.unionWith (max) (unM m) (unM n)

-- | Determines whether one monomial divides another
divides :: Ord v => Monomial ord v -> Monomial ord v -> Bool
divides m n = all (>= 0) . unM $ n ./. m

{-----------------------------------
 Monomial orders
 -----------------------------------}

type MonomialOrder ord v = Monomial ord v -> Monomial ord v -> Ordering

data Lex = Lex
data GrevLex = GrevLex
data Elimination = Elimination

-- | Class of elimination variables
class Ord v => Elim v where
  eliminate :: v -> Bool

-- | Lexicographic order
lexCompare :: Ord v => MonomialOrder ord v
lexCompare m n = case reverse $ filter (/= 0) . Map.elems . unM $ m ./. n of
        []            -> EQ
        (x:_) | x < 0 -> LT
        _             -> GT

-- | Graded reverse lexicographic ordering
grevlexCompare :: Ord v => MonomialOrder ord v
grevlexCompare m n
    | k /= l    = compare k l
    | otherwise = case filter (/= 0) . Map.elems . unM $ m ./. n of
        []            -> EQ
        (x:_) | x < 0 -> GT
        _             -> LT
    where k = degree m
          l = degree n

-- | Elimination ordering with a local ordering
eliminationBuilder :: (Ord v, Elim v) => MonomialOrder ord v -> MonomialOrder ord v
eliminationBuilder cmp m n =
  case cmp (Monomial mx) (Monomial nx) of
    EQ -> cmp (Monomial my) (Monomial ny)
    or -> or
  where (mx, my) = Map.partitionWithKey (\k _ -> eliminate k) $ unM m
        (nx, ny) = Map.partitionWithKey (\k _ -> eliminate k) $ unM n

-- | Default elimination order using local grevlex
eliminationCompare :: (Ord v, Elim v) => MonomialOrder ord v
eliminationCompare = eliminationBuilder grevlexCompare

instance Ord v => Ord (Monomial Lex v) where
  {-# INLINABLE compare #-}
  compare = lexCompare

instance Ord v => Ord (Monomial GrevLex v) where
  {-# INLINABLE compare #-}
  compare = grevlexCompare

instance (Ord v, Elim v) => Ord (Monomial Elimination v) where
  {-# INLINABLE compare #-}
  compare = eliminationCompare

{-----------------------------------
 Polynomials 
 -----------------------------------}

-- | Polynomials in variables /v/ over a ring /r/ and monomial group /m/
--
--   Assumes /r/ is some commutative ring
data Polynomial ord v r = Poly { getTerms :: !(Map (Monomial ord v) r) }
  deriving (Eq)

-- | Convenience types
type Multivariate     v r  = Polynomial GrevLex v r
type MultivariateElim v r  = Polynomial Elimination v r

{- Instances -}

instance (Ord r, Ord v, Ord (Monomial ord v)) => Ord (Polynomial ord v r) where
  compare p q = compare (getTerms p) (getTerms q)

instance (Ord v) => Degree (Polynomial ord v r) where
  degree (Poly t) = case Map.lookupMax t of
    Nothing      -> -1
    Just (m, _a) -> degree m

instance (Ord v) => Vars (Polynomial ord v r) where
  type Var (Polynomial ord v r) = v
  {-# INLINABLE vars #-}
  vars = foldr (Set.union) Set.empty . map vars . Map.keys . getTerms

instance (Ring r, Ord v) => Symbolic (Polynomial ord v r) where
  ofVar x = Poly $ Map.singleton (ofVar x) 1

instance (Ring r, Show v, Show r) => Show (Polynomial ord v r) where
  show p@(Poly t)
    | isZero p  = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs t)
    where showTerm (mono, coeff)
            | degree mono == 0 = show coeff
            | coeff == 1       = show mono
            | coeff == -1      = "-" ++ show mono
            | otherwise        = show coeff ++ show mono

instance (Ring r, Ord v, Ord (Monomial ord v)) => Num (Polynomial ord v r) where
  (+)         = curry (normalize . uncurry add)
  (*)         = curry (normalize . uncurry mult)
  negate      = Poly . Map.map negate . getTerms
  abs         = id
  signum      = id
  fromInteger = constant . fromInteger

instance (Ring r, Abelian r, Ord v, Ord (Monomial ord v)) => Abelian (Polynomial ord v r) where
  power i = normalize . Poly . Map.map (power i) . getTerms

instance (Ring r, Periodic r, Ord v, Ord (Monomial ord v)) => Periodic (Polynomial ord v r) where
  order = Map.foldr (\a -> lcm (order a)) 1 . getTerms

instance (Ring r, Ord v, IsString v) => IsString (Polynomial ord v r) where
  fromString s = ofVar (fromString s)

{- Accessors -}

-- | Get a list of the coefficients in grevlex order
coefficients :: Polynomial ord v r -> [r]
coefficients = Map.elems . getTerms

-- | Get the support in the monomial order
support :: Polynomial ord v r -> [Monomial ord v]
support = Map.keys . getTerms

-- | Get the terms in the monomial order
toTermList :: Polynomial ord v r -> [(r, Monomial ord v)]
toTermList = map swap . Map.toList . getTerms

-- | Retrieve the constant term
getConstant :: (Ring r, Ord v, Ord (Monomial ord v)) => Polynomial ord v r -> r
getConstant = Map.findWithDefault 0 mempty . getTerms

{- Tests -}

-- | Check if the polynomial is the zero function
isZero :: Polynomial ord v r -> Bool
isZero = Map.null . getTerms

-- | Check if the polynomial is a monomial
isMono :: Polynomial ord v r -> Bool
isMono = (1 >=) . Map.size . getTerms

-- | Check if the polynomial is constant
isConst :: Ord v => Polynomial ord v r -> Bool
isConst = (== [mempty]) . Map.keys . getTerms

-- | Check if a variable is used in the polynomial
contains :: Ord v => v -> Polynomial ord v r -> Bool
contains v = any (Set.member v . vars) . Map.keys . getTerms

{- Special forms -}

-- | Check if the polynomial is of the form /v/ for some variable /v/
asVar :: (Ring r, Ord v) => Polynomial ord v r -> Maybe v
asVar p = case map (\(r, m) -> (r, Set.toList (vars m))) rTerms of
  (1, [v]):[]  -> Just v
  otherwise    -> Nothing
  where rTerms = filter ((/= 0) . fst) $ toTermList p

{- Constructors -}

-- | Constant polynomial
constant :: (Ring r, Ord v) => r -> Polynomial ord v r
constant 0 = Poly $ Map.empty
constant a = Poly $ Map.singleton mempty a

-- | Construct the polynomial /m/ for a monomial /m/
ofMonomial :: (Ring r) => Monomial ord v -> Polynomial ord v r
ofMonomial m = Poly $ Map.singleton m 1

-- | Construct the polynomial /a*m/
ofTerm :: (Ring r) => (r, Monomial ord v) -> Polynomial ord v r
ofTerm (0, _) = Poly $ Map.empty
ofTerm (a, m) = Poly $ Map.singleton m a

-- | Construct the polynomial /a*m/
ofTermList :: (Ring r, Ord v, Ord (Monomial ord v)) => [(r, Monomial ord v)] -> Polynomial ord v r
ofTermList = Poly . Map.fromList . filter ((/= 0) . snd) . map swap

{- Transformations -}

-- | Normalize a multilinear polynomial
normalize :: (Ring r) => Polynomial ord v r -> Polynomial ord v r
normalize = Poly . Map.filter (0/=) . getTerms

-- | Drops the constant term. Useful for verification up to global phase
dropConstant :: (Ring r, Ord v, Ord (Monomial ord v)) => Polynomial ord v r -> Polynomial ord v r
dropConstant = Poly . (Map.delete mempty . getTerms)

-- | Cast a polynomial over ring /r/ to ring /s/
cast :: (r -> s) -> Polynomial ord v r -> Polynomial ord v s
cast f = Poly . Map.map f . getTerms

-- | Attempt to cast a polynomial over ring /r/ to ring /s/ via a partial function
castMaybe :: (r -> Maybe s) -> Polynomial ord v r -> Maybe (Polynomial ord v s)
castMaybe f = fmap Poly . mapM f . getTerms

-- | Collects just the terms of the polynomial satisfying a predicate
collectBy :: ((r, Monomial ord v) -> Bool) -> Polynomial ord v r -> Polynomial ord v r
collectBy f = Poly . Map.filterWithKey (curry $ f . swap) . getTerms

-- | Collects the terms of a polynomial containing a particular variable
collectVar :: Ord v => v -> Polynomial ord v r -> Polynomial ord v r
collectVar v = collectBy (\(_a, m) -> Set.member v $ vars m)

-- | Collects the terms of a polynomial containing a set of variables
collectVars :: Ord v => Set v -> Polynomial ord v r -> Polynomial ord v r
collectVars s = collectBy (\(_a, m) -> (vars m) `Set.isSubsetOf` s)

{- Arithmetic -}

-- | Scale a polynomial
scale :: (Ring r) => r -> Polynomial ord v r -> Polynomial ord v r
scale a
  | a == 0    = \_ -> Poly Map.empty
  | otherwise = Poly . Map.map (a*) . getTerms

-- | Add two polynomials
add :: (Ring r, Ord (Monomial ord v)) => Polynomial ord v r -> Polynomial ord v r -> Polynomial ord v r
add p = Poly . Map.unionWith (+) (getTerms p) . getTerms

-- | Multiply two polynomials
mult :: (Ring r, Ord v, Ord (Monomial ord v)) => Polynomial ord v r -> Polynomial ord v r -> Polynomial ord v r
mult p
  | isZero p  = \_ -> Poly Map.empty
  | otherwise = Map.foldrWithKey (\m a acc -> add acc $ mTerm m a) (Poly $ Map.empty) . getTerms
  where mTerm m a = Poly . Map.fromAscList . sumUp . groupMono . mBy m a . Map.toAscList $ tms
        mBy m a   = map $ \(m',a') -> (m<>m', a*a')
        groupMono = groupBy (\t t' -> fst t == fst t')
        sumUp     = map $ foldr1 (\(m,a) (_,a') -> (m,a+a'))
        tms       = getTerms p

-- | Performs the Euclidean division of a polynomial 'p' by a variables 'x', such that
--
--   @ p = 'ofVar' x * 'fst' ('varDiv' p x) + 'snd' ('varDiv' p x) @
divVar :: (Ord v, Ord (Monomial ord v)) => Polynomial ord v r -> v -> (Polynomial ord v r, Polynomial ord v r)
divVar p x = (Poly $ Map.mapKeys (./. (ofVar x)) qTerms, Poly rTerms)
  where (qTerms, rTerms) = Map.partitionWithKey f $ getTerms p
        f m _a           = Set.member x $ vars m

-- | Takes the quotient of 'p'/'x'
quotVar :: (Ord v, Ord (Monomial ord v)) => v -> Polynomial ord v r -> Polynomial ord v r
quotVar x = fst . (flip divVar) x

-- | Takes the remainder of 'p'/'x'
remVar :: (Ord v, Ord (Monomial ord v)) => v -> Polynomial ord v r -> Polynomial ord v r
remVar x = snd . (flip divVar) x

-- | Factors out all trivial factors
factorizeTrivial :: (Ring r, Ord v, Ord (Monomial ord v)) => Polynomial ord v r -> ([Polynomial ord v r], Polynomial ord v r)
factorizeTrivial p = Set.foldr tryDiv ([], p) $ vars p
  where tryDiv x  (acc, poly) =
          let (q, r) = divVar poly x in
            if isZero r then ((ofVar x):acc, q) else (acc, poly)

{- Substitutions -}

-- | Rename variables according to a variable map
--
--   Note: Less general
rename :: (Ord v, Ord (Monomial ord v)) => (v -> v) -> Polynomial ord v r -> Polynomial ord v r
rename sub = Poly . Map.mapKeys (monomial . map sub . unMonomial) . getTerms

-- | Rename variables according to a monotonic variable map
--
--   Note: Less general
renameMonotonic :: Ord v => (v -> v) -> Polynomial ord v r -> Polynomial ord v r
renameMonotonic sub = Poly . Map.mapKeysMonotonic (monomial . map sub . unMonomial) . getTerms

-- | Substitute a variable with a polynomial
subst :: (Ring r, Ord v, Ord (Monomial ord v)) => v -> Polynomial ord v r -> Polynomial ord v r -> Polynomial ord v r
subst v p = substMany (\v' -> if v' == v then p else ofVar v')

-- | Simultaneous substitution of variables with polynomials
substMany :: (Ring r, Ord v, Ord (Monomial ord v)) => (v -> Polynomial ord v r) -> Polynomial ord v r -> Polynomial ord v r
substMany sub = normalize . Map.foldrWithKey (\m a -> add (substInMono (a,m))) zero . getTerms
  where substInMono (a,m) = scale a $ foldr (mult) one (map sub $ unMonomial m)

{-

-- | Substitute a variable with a monomial
substVarMono :: (Ord v, Eq r, Num r, ReprC repr) =>
             v -> Monomial v repr -> Polynomial r m -> Polynomial v r repr
substVarMono v m = M . Map.mapKeys (Set.foldr substVar mempty . vars) . getTerms
  where substVar v' acc
          | v == v'   = acc <> m
          | otherwise = acc <> monomial [v']

-- | Find a necessary substitution solving @p = 0@ over a field
solveForX :: (Ord v, Eq r, Fractional r, ReprC repr) =>
             Polynomial r m -> [(v, Polynomial v r repr)]
solveForX p = mapMaybe checkTerm . filter (\(_a,m) -> degree m == 1) $ toTermList p
  where checkTerm (a,m) =
          let v  = Set.elemAt 0 $ vars m
              p' = p - ofTerm (a,m)
          in
            if not (contains v p')
            then Just (v, scale (recip a) p')
            else Nothing

-- | Return a list of solutions to @p = 0@ over a field
allSolutions :: (Ord v, Eq r, Fractional r, Abelian r) =>
             Polynomial v r 'Mult -> [(v, Polynomial v r 'Mult)]
allSolutions = concatMap solveForX . factorize

-- | Return a single solution to @p = 0@
getSolution :: (Ord v, Eq r, Fractional r, Abelian r) =>
             Polynomial v r 'Mult -> (v, Polynomial v r 'Mult)
getSolution = head . concatMap solveForX . factorize

-}

{- Testing-}
{-
data EVar = XVar String | YVar String deriving (Eq)

getVar :: EVar -> String
getVar (XVar x) = x
getVar (YVar x) = x

instance IsString EVar where
  fromString = XVar

instance Ord EVar where
  compare s t = compare (getVar t) (getVar s)

instance Show EVar where
  show = getVar

instance Elim EVar where
  eliminate (XVar x) = False
  eliminate (YVar x) = True

--x1, x2, x3, y1, y2, y3 :: Multivariate EVar FF2
x1,x2,x3,y1,y2,y3 :: EVar
x1 = XVar "x1"
x2 = XVar "x2"
x3 = XVar "x3"
y1 = YVar "y1"
y2 = YVar "y2"
y3 = YVar "y3"

combinations :: [a] -> [[a]]
combinations []     = [[]]
combinations (x:xs) = combinations xs ++ (map (x:) $ combinations xs)

varOrd1 :: [Monomial GrevLex EVar]
varOrd1 = reverse $ sort $ map monomial $ combinations [x1,x2,x3]

varOrd2 :: [Monomial Elimination EVar]
varOrd2 = reverse $ sort $ map monomial $ combinations [x1,x2,x3,y1,y2,y3]

varOrd3 :: [Monomial GrevLex EVar]
varOrd3 = reverse $ sort $ map monomial $ [[x1,x1],[x1,x2],[x1,x3],[x2,x2],[x2,x3],[x3,x3]]

varOrd4 :: [Monomial Lex EVar]
varOrd4 = reverse $ sort $ map monomial $ [[x1,x1],[x1,x2],[x1,x3],[x2,x2],[x2,x3],[x3,x3]]

varOrd5 :: [Monomial Elimination EVar]
varOrd5 = reverse $ sort $ map monomial $ [[y1,x1],[x1,y2],[x1,x3],[y2,y2],[x2,y3],[x3,x3]]
-}
