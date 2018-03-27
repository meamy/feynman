module Feynman.Algebra.Polynomial where

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid ((<>))
import Data.Maybe

import Data.List
import Data.Bits

import Data.Ratio

import Algebra.Base

{- Monomial representation -}
-- TODO: Substitutions need to find a degree 1 monomial, which (if found) requires
-- two O(n) operations, to find and subsequently get the variable number. We could
-- speed this up by adding a second constructor explicitly for degree 1 monomials.
-- There's a tradeoff as Monomial can no longer be unboxed
type Monomial = Set String

monomial :: [String] -> Monomial
monomial = Set.fromList

monomialVars :: Monomial -> [String]
monomialVars = Set.elems

monomialDegree :: Monomial -> Int
monomialDegree = Set.size

inMonomial :: String -> Monomial -> Bool
inMonomial = Set.member

multMonomial :: Monomial -> Monomial -> Monomial
multMonomial = Set.union

mapMonomial :: (String -> String) -> Monomial -> Monomial
mapMonomial = Set.map

reduceMonomial :: String -> Monomial -> Monomial
reduceMonomial = Set.delete

firstVar :: Monomial -> String
firstVar = Set.elemAt 0

{- Multi-linear polynomials -}
data Multilinear a = Multilinear {
  terms :: !(Map Monomial a)
  } deriving (Ord)

instance (Eq a, Ring a) => Eq (Multilinear a) where
  p == q = terms (simplify p) == terms (simplify q)

instance (Eq a, Ring a, Show a) => Show (Multilinear a) where
  show p@(Multilinear terms)
    | isZero p    = "0"
    | p == one    = "1"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs terms)
    where showTerm (m, a)
            | monomialDegree m == 0 = show a
            | a == zero             = show a
            | a == one              = showMono m
            | otherwise             = (show a) ++ (showMono m)
          showMono = concat . monomialVars

instance (Eq a, Ring a) => Num (Multilinear a) where
  (+) = add
  (*) = mult
  negate p = p { terms = Map.map negate (terms p) }
  abs    p = p { terms = Map.map abs (terms p) }
  signum p = p
  fromInteger i = constant (fromInteger i)

instance (Eq a, Ring a) => Abelian (Multilinear a) where
  zero  = constant zero
  pow i = Multilinear . Map.map (pow i) . terms

instance (Eq a, Ring a) => Ring (Multilinear a) where
  one = constant one

instance (Eq a, Ring a) => Monoid (Multilinear a) where
  mempty  = zero
  mappend = (+)

degree :: (Eq a, Ring a) => Multilinear a -> Int
degree p
  | isZero p    = -1
  | otherwise = maximum $ map degTerm $ Map.toList $ terms p
  where degTerm (m, k) = if k == zero then -1 else monomialDegree m

coefficients :: Multilinear a -> [a]
coefficients = Map.elems . terms

-- This should really be tracked by the polynomial itself,
-- but it's not used often so screw it for now
vars :: Multilinear a -> [String]
vars = Set.toList . Map.foldlWithKey (\a k _ -> Set.union a k) Set.empty . terms

{- Tests -}

isZero :: Multilinear a -> Bool
isZero = Map.null . terms

isMono :: Multilinear a -> Bool
isMono = (1 >=) . Map.size . terms

appearsIn :: String -> Multilinear a -> Bool
appearsIn v (Multilinear terms) = any (v `inMonomial`) . Map.keys $ terms

{- Constructors -}
constant :: Num a => a -> Multilinear a
constant a = Multilinear $ Map.singleton (monomial []) a

ofTerm :: (Eq a, Ring a) => a -> [String] -> Multilinear a
ofTerm a xs
  | a == zero = zero
  | otherwise = Multilinear $ Map.singleton (monomial xs) a

ofTermDirect :: (Eq a, Ring a) => a -> Monomial -> Multilinear a
ofTermDirect a m = Multilinear $ Map.singleton m a

ofVar :: (Eq a, Ring a) => String -> Multilinear a
ofVar v = ofTerm one [v]

ofMonomial :: (Eq a, Ring a) => [String] -> Multilinear a
ofMonomial xs = ofTerm one xs

{- Operators -}

getConstant :: (Eq a, Ring a) => Multilinear a -> a
getConstant = Map.findWithDefault zero (monomial []) . terms

scale :: (Eq a, Ring a) => a -> Multilinear a -> Multilinear a
scale a p
  | a == zero = zero
  | otherwise = Multilinear $ Map.map (a *) $ terms p

add :: (Eq a, Ring a) => Multilinear a -> Multilinear a -> Multilinear a
add p q = Multilinear $ Map.unionWith (+) (terms p) (terms q)

mult :: (Eq a, Ring a) => Multilinear a -> Multilinear a -> Multilinear a
mult p q = Map.foldlWithKey' f zero (terms p)
    where f acc m a         =
            let amq = Multilinear $ Map.foldlWithKey' (g m a) Map.empty (terms q) in
              add acc amq
          g m a terms m' a' = Map.alter (h $ a * a') (multMonomial m m') terms
          h a b             = case b of
            Nothing -> Just a
            Just c  -> Just $ a + c

{- Substitutions -}

-- Rename some variables
-- NOTE: Doesn't check for overlap
rename :: (Eq a, Ring a) => Map String String -> Multilinear a -> Multilinear a
rename sub p = simplify $ Multilinear terms'
  where terms' = Map.mapKeys (mapMonomial (sub!)) $ terms p

renameMonotonic :: (Eq a, Ring a) => Map String String -> Multilinear a -> Multilinear a
renameMonotonic sub p = simplify $ Multilinear terms'
  where terms' = Map.mapKeysMonotonic (mapMonomial (sub!)) $ terms p

-- Substitute a variable with a Boolean expression
subst :: (Eq a, Ring a) => String -> Multilinear Z2 -> Multilinear a -> Multilinear a
subst v exp (Multilinear terms) = simplify $ Map.foldlWithKey' f zero terms
  where f p' m a
          | v `inMonomial` m = p' + (distribute a $ ofTermDirect one (reduceMonomial v m) * exp)
          | otherwise        = p' + (ofTermDirect a m)

-- Simultaneous substitution
substMany :: (Eq a, Ring a) => Map String (Multilinear Z2) -> Multilinear a -> Multilinear a
substMany sub p@(Multilinear terms) = simplify $ Map.foldlWithKey' f zero terms
  where f p' m a = p' + (distribute a $ foldl' (*) one (map g $ monomialVars m))
        g v      = Map.findWithDefault (ofVar v) v sub

-- Get possible variable substitutions giving p = 0
solveForX :: (Eq a, Field a) => Multilinear a -> [(String, Multilinear a)]
solveForX p = mapMaybe f . Map.toAscList . terms . simplify $ p
  where f (m, a) =
          let v  = firstVar m 
              p' = simplify $ p - ofTermDirect a m
          in
            if monomialDegree m == 1 && not (appearsIn v p')
            then Just (v, scale (recip a) p')
            else Nothing

{- Transformations -}

simplify :: (Eq a, Ring a) => Multilinear a -> Multilinear a
simplify p = p { terms = Map.filter (zero /=) $ terms p }

-- NOTE: the variable removal here isn't monotonic wrt the set ordering, hence the O(nlogn) map
factorOut :: String -> Multilinear a -> Multilinear a
factorOut v p = p { terms = terms' }
  where terms' = Map.mapKeys (reduceMonomial v) . Map.filterWithKey (\m _ -> v `inMonomial` m) $ terms p

splitBy :: String -> Multilinear a -> (Multilinear a, Multilinear a)
splitBy v p = (p { terms = posTerms }, p { terms = negTerms })
  where (posTerms, negTerms) = Map.partitionWithKey (\m _ -> v `inMonomial` m) $ terms p

removeVar :: String -> Multilinear a -> Multilinear a
removeVar v p = p { terms = terms' }
  where terms' = Map.filterWithKey (\m _ -> not $ inMonomial v m) $ terms p

distributeM :: (Eq a, Ring a) => a -> [Monomial] -> Multilinear a
distributeM a [] = zero
distributeM a (m:xs)
  | a == zero = zero
  | otherwise          = p + (distributeM a xs) + distributeM (-(pow 2 a)) (mmult m xs)
  where p = Multilinear $ Map.singleton m a
        mmult m = map (multMonomial m)

distribute :: (Eq a, Ring a) => a -> Multilinear Z2 -> Multilinear a
distribute a = distributeM a . Map.keys . terms . simplify

convert :: (a -> b) -> Multilinear a -> Multilinear b
convert f p = p { terms = Map.map f $ terms p }

convertMaybe :: (a -> Maybe b) -> Multilinear a -> Maybe (Multilinear b)
convertMaybe f p = mapM f (terms p) >>= \terms' -> return $ p { terms = terms' }

{- Debug -}

{- Tests -}

x0 = ofVar "x0" :: Multilinear Z2 
x1 = ofVar "x1" :: Multilinear Z2
x2 = ofVar "x2" :: Multilinear Z2
x3 = ofVar "x3" :: Multilinear Z2
