{-# LANGUAGE TypeFamilies #-}

{-|
Module      : Polynomial
Description : Polynomial base
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial(Degree(..), Vars(..)) where

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

{-----------------------------------
 Type classes
 -----------------------------------}

-- | Class of things that have a degree
class Degree a where
  degree :: a -> Int

-- | Class of things that have variables
class Vars a where
  type Var a
  vars :: a -> Set (Var a)

-- | Class of rings for the purpose of polynomials
class (Eq r, Num r) => Ring r

-- | Class of groups for the purpose of polynomials
class (Monoid m) => Group m where
  (./.) :: m -> m -> m

-- | Class of symbolic values
class Vars a => Symbolic a where
  ofVar :: Var a -> a

{-----------------------------------
 Monomials
 -----------------------------------}

-- | Class of monomials over a variable type.
--
--   Ordered terms over variables with a group structure
class (Degree m, Ord (Var m), Ord m, Group m, Symbolic m) => Monomial m

-- | Construct a monomial
monomial :: Monomial m => [Var m] -> m
monomial = foldr (\a -> ((ofVar a) <>)) mempty

{-----------------------------------
 Polynomials 
 -----------------------------------}

-- | Polynomials in variables /v/ over a ring /r/ and monomial group /m/
--
--   Assumes /r/ is some commutative ring
data Polynomial r m = Poly { getTerms :: !(Map m r) }
  deriving (Eq, Ord)

instance (Monomial m) => Degree (Polynomial r m) where
  degree (Poly t) = case Map.lookupMax t of
    Nothing      -> -1
    Just (m, _a) -> degree m

instance (Monomial m) => Vars (Polynomial r m) where
  type Var (Polynomial r m) = Var m
  {-# INLINABLE vars #-}
  vars = foldr (Set.union) Set.empty . map vars . Map.keys . getTerms

instance (Ring r, Monomial m) => Symbolic (Polynomial r m) where
  ofVar x = Poly $ Map.singleton (ofVar x) 1

instance (Ring r, Monomial m, Show r, Show m) => Show (Polynomial r m) where
  show p@(Poly t)
    | isZero p  = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs t)
    where showTerm (mono, coeff)
            | degree mono == 0 = show coeff
            | coeff == 1       = show mono
            | coeff == -1      = "-" ++ show mono
            | otherwise        = show coeff ++ show mono

{- Accessors -}

-- | Get a list of the coefficients in grevlex order
coefficients :: Polynomial r m -> [r]
coefficients = Map.elems . getTerms

-- | Get the support in the monomial order
support :: Polynomial r m -> [m]
support = Map.keys . getTerms

-- | Get the terms in the monomial order
toTermList :: Polynomial r m -> [(r, m)]
toTermList = map swap . Map.toList . getTerms

-- | Retrieve the constant term
getConstant :: (Ring r, Monomial m) => Polynomial r m -> r
getConstant = Map.findWithDefault 0 mempty . getTerms

{- Tests -}

-- | Check if the polynomial is the zero function
isZero :: Polynomial r m -> Bool
isZero = Map.null . getTerms

-- | Check if the polynomial is a monomial
isMono :: Polynomial r m -> Bool
isMono = (1 >=) . Map.size . getTerms

-- | Check if the polynomial is constant
isConst :: Monomial m => Polynomial r m -> Bool
isConst = (== [mempty]) . Map.keys . getTerms

-- | Check if a variable is used in the polynomial
contains :: Monomial m => (Var m) -> Polynomial r m -> Bool
contains v = any (Set.member v . vars) . Map.keys . getTerms

{- Special forms -}

-- | Check if the polynomial is of the form /v/ for some variable /v/
asVar :: (Ring r, Monomial m) => Polynomial r m -> Maybe (Var m)
asVar p = case map (\(r, m) -> (r, Set.toList (vars m))) rTerms of
  (1, [v]):[]  -> Just v
  otherwise    -> Nothing
  where rTerms = filter ((/= 0) . fst) $ toTermList p

{- Constructors -}

-- | Constant polynomial
constant :: (Ring r, Monomial m) => r -> Polynomial r m
constant 0 = Poly $ Map.empty
constant a = Poly $ Map.singleton mempty a

-- | Construct the polynomial /m/ for a monomial /m/
ofMonomial :: (Ring r, Monomial m) => m -> Polynomial r m
ofMonomial m = Poly $ Map.singleton m 1

-- | Construct the polynomial /a*m/
ofTerm :: (Ring r, Monomial m) => (r, m) -> Polynomial r m
ofTerm (0, _) = Poly $ Map.empty
ofTerm (a, m) = Poly $ Map.singleton m a

-- | Construct the polynomial /a*m/
ofTermList :: (Ring r, Monomial m) => [(r, m)] -> Polynomial r m
ofTermList = Poly . Map.fromList . filter ((/= 0) . snd) . map swap

{- Arithmetic -}

-- | Scale a polynomial
scale :: (Ring r) => r -> Polynomial r m -> Polynomial r m
scale a
  | a == 0    = \_ -> Poly Map.empty
  | otherwise = Poly . Map.map (a*) . getTerms

-- | Add two polynomials
add :: (Ring r, Monomial m) => Polynomial r m -> Polynomial r m -> Polynomial r m
add p = Poly . Map.unionWith (+) (getTerms p) . getTerms

-- | Multiply two polynomials
mult :: (Ring r, Monomial m) => Polynomial r m -> Polynomial r m -> Polynomial r m
mult p
  | isZero p  = \_ -> Poly Map.empty
  | otherwise = Map.foldrWithKey (\m a acc -> add acc $ multTerm m a) (Poly $ Map.empty) . getTerms
  where multTerm m a = Poly . Map.fromAscList . sumUp . groupMono . multBy m a . Map.toAscList $ tms
        multBy m a   = map $ \(m',a') -> (m<>m', a*a')
        groupMono    = groupBy (\t t' -> fst t == fst t')
        sumUp        = map $ foldr1 (\(m,a) (_,a') -> (m,a+a'))
        tms          = getTerms p

{-
-- | Monomials with graded lexicographic (grevlex) order
newtype Monomial v (repr :: Repr) = Monomial { vars :: Set v } deriving (Eq)

instance Ord v => Ord (Monomial v repr) where
  {-# INLINABLE compare #-}
  compare m n
    | k /= l    = compare k l
    | otherwise = compare (vars m) (vars n)
    where k = degree m
          l = degree n

instance Degree (Monomial v repr) where
  {-# INLINABLE degree #-}
  degree = Set.size . vars

instance Ord v => Vars (Monomial v repr) where
  type Var (Monomial v repr) = v
  {-# INLINABLE vars #-}
  vars = vars

showImpl :: Show v => ReprWit repr -> Monomial v repr -> String
showImpl WitAdd  = intercalate Unicode.oplus . map show . Set.toList . vars
showImpl WitMult = concatMap show . Set.toList . vars

instance (Show v, ReprC repr) => Show (Monomial v repr) where
  show = showImpl witRepr

mappendImpl :: Ord v => ReprWit repr -> Monomial v repr -> Monomial v repr -> Monomial v repr
mappendImpl WitMult m = Monomial . Set.union (vars m) . vars
mappendImpl WitAdd m  = Monomial . symDiff (vars m) . vars
  where symDiff a b = Set.difference (Set.union a b) (Set.intersection a b)

instance (Ord v, ReprC repr) => Semigroup (Monomial v repr) where
  (<>) = mappendImpl witRepr

instance (Ord v, ReprC repr) => Monoid (Monomial v repr) where
  mempty  = Monomial Set.empty
  mappend = (<>)

-- | Convenience types
type PhasePolynomial v r  = Polynomial v r 'Add
type PseudoBoolean v r    = Polynomial v r 'Mult
type SBool v              = Polynomial v FF2 'Mult

instance (Ord v, Eq r, Num r, ReprC repr) => Num (Polynomial r m) where
  (+) = \p -> normalize . addM p
  (*) = \p -> normalize . multM witRepr p
  negate (M t) = M $ Map.map negate t
  abs    = id
  signum = id
  fromInteger 0 = M $ Map.empty
  fromInteger i = M . Map.singleton (Monomial Set.empty) $ fromInteger i

instance (Ord v, Eq r, Abelian r, ReprC repr) => Abelian (Polynomial r m) where
  power i = normalize . M . Map.map (power i) . getTerms

instance (Ord v, Eq r, Periodic r, ReprC repr) => Periodic (Polynomial r m) where
  order = Map.foldr (\a -> lcm (order a)) 1 . getTerms

instance (Ord v, IsString v, Eq r, Num r, ReprC repr) => IsString (Polynomial r m) where
  fromString s = ofVar (fromString s)



-- | Multiply two polynomials with the same representation
multM :: (Ord v, Eq r, Num r) =>
         ReprWit repr -> Polynomial r m -> Polynomial v r repr -> Polynomial v r repr
multM wit p q = case wit of
  WitAdd  -> error "Error: multiplying additive phase polynomials"
  WitMult -> multImpl p q

multImpl :: (Ord v, Eq r, Num r) =>
            Polynomial v r 'Mult -> Polynomial v r 'Mult -> Polynomial v r 'Mult
multImpl p
  | p == 0           = \_ -> 0
  | otherwise        = Map.foldrWithKey (\m a acc -> addM acc $ multTerm m a) zero . getTerms
  where multTerm m a = M . Map.fromAscList . sumUp . groupMono . multBy m a . Map.toAscList $ tms
        multBy m a   = map $ \(m',a') -> (m<>m', a*a')
        groupMono    = groupBy (\t t' -> fst t == fst t')
        sumUp        = map $ foldr1 (\(m,a) (_,a') -> (m,a+a'))
        tms          = getTerms p

-- | Performs the Euclidean division of a polynomial 'p' by a variables 'x', such that
--
--   @ p = 'ofVar' x * 'fst' ('varDiv' p x) + 'snd' ('varDiv' p x) @
divVar :: Ord v => Polynomial v r 'Mult -> v -> (Polynomial v r 'Mult, Polynomial v r 'Mult)
divVar p x = (M $ Map.mapKeys (Monomial . Set.delete x . vars) qTerms, M rTerms)
  where (qTerms, rTerms) = Map.partitionWithKey f $ getTerms p
        f m _a           = Set.member x $ vars m

-- | Takes the quotient of 'p'/'x'
quotVar :: Ord v => v -> Polynomial v r 'Mult -> Polynomial v r 'Mult
quotVar x = M . Map.mapKeys (Monomial . Set.delete x . vars) . takeQuotient . getTerms
  where takeQuotient = Map.filterWithKey (\m _a -> Set.member x $ vars m)

-- | Takes the remainder of 'p'/'x'
remVar :: Ord v => v -> Polynomial v r 'Mult -> Polynomial v r 'Mult
remVar x = M . Map.filterWithKey (\m _a -> not $ Set.member x $ vars m) . getTerms

-- | Factors out all trivial factors
factorizeTrivial :: (Ord v, Eq r, Num r) =>
                    Polynomial v r 'Mult -> ([Polynomial v r 'Mult], Polynomial v r 'Mult)
factorizeTrivial p = Set.foldr tryDiv ([], p) $ vars p
  where tryDiv x  (acc, poly) =
          let (q, r) = divVar poly x in
            if isZero r then ((ofVar x):acc, q) else (acc, poly)

-- | Factorize a multilinear polynomial into irreducibles. Algorithm due to
--   A. Shpilka & I. Volkovich, /On the Relation between Polynomial Identity
--   Testing and Finding Variable Disjoint Factors/
factorize :: (Ord v, Eq r, Abelian r) => Polynomial v r 'Mult -> [Polynomial v r 'Mult]
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
normalize :: (Ord v, Eq r, Num r) => Polynomial r m -> Polynomial v r repr
normalize = M . Map.filter (0/=) . getTerms

-- | Drops the constant term. Useful for verification up to global phase
dropConstant :: (Ord v, Eq r, Num r) => Polynomial r m -> Polynomial v r repr
dropConstant = M . (Map.delete (Monomial Set.empty) . getTerms)

-- | Cast a polynomial over ring /r/ to ring /s/
cast :: (r -> s) -> Polynomial r m -> Polynomial v s repr
cast f = M . Map.map f . getTerms

-- | Attempt to cast a polynomial over ring /r/ to ring /s/ via a partial function
castMaybe :: (r -> Maybe s) -> Polynomial r m -> Maybe (Polynomial v s repr)
castMaybe f = fmap M . mapM f . getTerms

-- | Collects just the terms of the polynomial satisfying a predicate
collectBy :: ((r, Monomial v repr) -> Bool) -> Polynomial r m -> Polynomial v r repr
collectBy f = M . Map.filterWithKey (curry $ f . swap) . getTerms

-- | Collects the terms of a polynomial containing a particular variable
collectVar :: Ord v => v -> Polynomial r m -> Polynomial v r repr
collectVar v = collectBy (\(_a, m) -> Set.member v $ vars m)

-- | Collects the terms of a polynomial containing a set of variables
collectVars :: Ord v => Set v -> Polynomial r m -> Polynomial v r repr
collectVars s = collectBy (\(_a, m) -> (vars m) `Set.isSubsetOf` s)

{- Substitutions -}

-- | Rename variables according to a variable map
rename :: (Ord v, Ord v') => (v -> v') -> Polynomial r m -> Polynomial v' r repr
rename sub = M . Map.mapKeys (Monomial . Set.map sub . vars) . getTerms

-- | Rename variables according to a monotonic variable map
renameMonotonic :: (Ord v, Ord v') => (v -> v') -> Polynomial r m -> Polynomial v' r repr
renameMonotonic sub = M . Map.mapKeysMonotonic (Monomial . Set.map sub . vars) . getTerms

-- | Substitute a (Boolean) variable with a (Boolean) polynomial
subst :: (Ord v, Eq r, Abelian r) => v -> SBool v -> Polynomial v r 'Mult -> Polynomial v r 'Mult
subst v p = substMany (\v' -> if v' == v then p else ofVar v')

-- | Simultaneous substitution of variables with polynomials
substMany :: (Ord v, Eq r, Abelian r) => (v -> SBool v) -> Polynomial v r 'Mult -> Polynomial v r 'Mult
substMany sub = normalize . Map.foldrWithKey (\m a acc -> addM acc $ substInMono m a) zero . getTerms
  where substInMono m a = distribute a $ foldr (multImpl) one (map sub . Set.toList $ vars m)

-- | Substitute a (Boolean, multiplicative) monomial with a (Boolean) polynomial
substMonomial :: (Ord v, Eq r, Abelian r) => [v] -> SBool v -> Polynomial v r 'Mult -> Polynomial v r 'Mult
substMonomial xs p = normalize . Map.foldrWithKey (\m a acc -> addM acc $ substMonoInMono m a) zero . getTerms
  where m = Set.fromList xs
        substMonoInMono m' a
          | not (m `Set.isSubsetOf` (vars m')) = ofTerm (a,m')
          | otherwise = distribute a $ p * ofMonomial (Monomial $ Set.difference (vars m') m)

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

{- Pseudo-boolean specific transformations -}

-- | Translate a monomial to a Boolean polynomial
liftImpl :: Ord v => ReprWit repr -> Monomial v repr -> SBool v
liftImpl WitMult = M . (flip Map.singleton) 1
liftImpl WitAdd  = ofTermList . zip (repeat 1) . Set.toList . Set.map f . vars
  where f = Monomial . Set.singleton

-- | Translate an additive monomial to a Boolean polynomial
liftMonomial :: (Ord v, ReprC repr) => Monomial v repr -> SBool v
liftMonomial = liftImpl witRepr

-- | Translate a Boolean polynomial into any ring (in this case, Z-module)
lift :: (Ord v, Eq r, Abelian r) => SBool v -> Polynomial v r 'Mult
lift = distribute 1

-- | Distribute a ring element over a monomial according to the equation
-- 
-- > axy = a/2x + a/2y - a/2(x + y)
--
unDistribute :: (Ord v, Eq r, Num r, Dyadic r) => r -> Monomial v 'Mult -> Polynomial v r 'Add
unDistribute a' = go a' . Set.toList . vars
  where go 0 _        = zero
        go a []       = constant a
        go a [x]      = ofTerm (a, Monomial $ Set.singleton x)
        go a (x:y:xs) =
          let recTerm = go (negate $ divTwo a) $ x:xs
              sub     = Monomial $ Set.fromList [x, y]
          in
            go (divTwo a) (x:xs) + go (divTwo a) (y:xs) + substVarMono x sub recTerm

-- | Non-recursive exclusion-inclusion formula
excInc :: (Ord v, Eq r, Dyadic r) => Monomial v 'Mult -> Polynomial v r 'Add
excInc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            fromDyadic $ dyadic (if n `mod` 2 == 0 then -1 else 1) (Set.size s - 1)

-- | Distribute a ring element over a Boolean polynomial according to the equation
-- 
-- > a(x + y) = ax + ay -2axy
--
distribute :: (Ord v, Eq r, Abelian r) => r -> SBool v -> Polynomial v r 'Mult
distribute a' = go a' . Map.keys . getTerms . normalize
  where go 0 _      = zero
        go a []     = zero
        go a [m]    = ofTerm (a,m)
        go a (m:xs) = ofTerm (a,m) + (go a xs) + (go (power (-2) a) $ map (m <>) xs)

-- | Non-recursive inclusion-exclusion formula
incExc :: (Ord v, Eq r, Abelian r) => Monomial v 'Add -> Polynomial v r 'Mult
incExc (Monomial s) = ofTermList [(go s', Monomial s') | s' <- Set.toList $ Set.powerSet s]
  where go subset =
          let n = Set.size subset in
            if n `mod` 2 == 0 then power (-1 `shiftL` (n-1)) 1 else power (1 `shiftL` (n-1)) 1

-- | Perform the (pseudo-Boolean) Fourier transform
fourier :: (Ord v, Eq r, Dyadic r) => Polynomial v r 'Mult -> Polynomial v r 'Add
fourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ unDistribute a m

-- | Perform the (pseudo-Boolean) inverse Fourier transform
invFourier :: (Ord v, Eq r, Abelian r) => Polynomial v r 'Add -> Polynomial v r 'Mult
invFourier = normalize . Map.foldrWithKey addTerm zero . getTerms
  where addTerm m a acc = addM acc $ distribute a (liftMonomial m)

-- | Canonicalize an additive multilinear polynomial
canonicalize :: (Ord v, Eq r, Dyadic r, Abelian r) => Polynomial v r 'Add -> Polynomial v r 'Add
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

y0 = ofVar (IVar ("y",0)) :: Polynomial IVar DMod2 'Mult
y1 = ofVar (IVar ("y",1)) :: Polynomial IVar DMod2 'Mult
y2 = ofVar (IVar ("y",2)) :: Polynomial IVar DMod2 'Mult
y3 = ofVar (IVar ("y",3)) :: Polynomial IVar DMod2 'Mult
y4 = ofVar (IVar ("y",4)) :: Polynomial IVar DMod2 'Mult
y5 = ofVar (IVar ("y",5)) :: Polynomial IVar DMod2 'Mult
y6 = ofVar (IVar ("y",6)) :: Polynomial IVar DMod2 'Mult
y7 = ofVar (IVar ("y",7)) :: Polynomial IVar DMod2 'Mult
y8 = ofVar (IVar ("y",8)) :: Polynomial IVar DMod2 'Mult
y9 = ofVar (IVar ("y",9)) :: Polynomial IVar DMod2 'Mult
-}
