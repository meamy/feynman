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

{- Numeric instance for Boolean polynomials -}
-- NOTE: "from" functions aren't homomorphic
instance Num Bool where
  (+)           = xor
  (*)           = (&&)
  negate        = id
  abs           = id
  signum        = id
  fromInteger i = if i `mod` 2 == 0 then False else True

instance Fractional Bool where
  recip          = id
  (/)            = (*)
  fromRational i = fromInteger (numerator i) / fromInteger (denominator i)

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

emptyMonomial :: Monomial -> Bool
emptyMonomial = (== Set.empty)

{- Multi-linear polynomials -}
data Multilinear a = Multilinear {
  terms :: !(Map Monomial a)
  } deriving (Ord)

instance (Eq a, Num a) => Eq (Multilinear a) where
  p == q = terms (simplify p) == terms (simplify q)

instance (Eq a, Num a, Show a) => Show (Multilinear a) where
  show p@(Multilinear terms)
    | isZero p    = "0"
    | p == one    = "1"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs terms)
    where showTerm (m, a)
            | monomialDegree m == 0 = show a
            | a == fromInteger 0    = show a
            | a == fromInteger 1    = showMono m
            | otherwise             = (show a) ++ (showMono m)
          showMono m = "[" ++ (concat . monomialVars $ m) ++ "]"

degree :: (Eq a, Num a) => Multilinear a -> Int
degree p
  | isZero p    = -1
  | otherwise = maximum $ map degTerm $ Map.toList $ terms p
  where degTerm (m, k) = if k == fromInteger 0 then -1 else monomialDegree m

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

zero :: Multilinear a
zero = Multilinear Map.empty

one :: Num a => Multilinear a
one = constant $ fromInteger 1

constant :: Num a => a -> Multilinear a
constant a = Multilinear $ Map.singleton (monomial []) a

ofTerm :: (Eq a, Num a) => a -> [String] -> Multilinear a
ofTerm a xs
  | a == fromInteger 0 = zero
  | otherwise          = Multilinear $ Map.singleton (monomial xs) a

ofTermDirect :: (Eq a, Num a) => a -> Monomial -> Multilinear a
ofTermDirect a m = Multilinear $ Map.singleton m a

ofVar :: (Eq a, Num a) => String -> Multilinear a
ofVar v = ofTerm (fromInteger 1) [v]

ofMonomial :: (Eq a, Num a) => [String] -> Multilinear a
ofMonomial xs = ofTerm (fromInteger 1) xs

{- Operators -}

getConstant :: (Eq a, Num a) => Multilinear a -> a
getConstant = Map.findWithDefault (fromInteger 0) (monomial []) . terms

dropConstant :: (Eq a, Num a) => Multilinear a -> Multilinear a
dropConstant = Multilinear . (Map.delete (monomial []) . terms)

scale :: (Eq a, Num a) => a -> Multilinear a -> Multilinear a
scale a p
  | a == fromInteger 0 = zero
  | otherwise          = Multilinear $ Map.map (a *) $ terms p

add :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
add p q = Multilinear $ Map.unionWith (+) (terms p) (terms q)

mult :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
mult p q = Map.foldlWithKey' f zero (terms p)
    where f acc m a         =
            let amq = Multilinear $ Map.foldlWithKey' (g m a) Map.empty (terms q) in
              add acc amq
          g m a terms m' a' = Map.alter (h $ a * a') (multMonomial m m') terms
          h a b             = case b of
            Nothing -> Just a
            Just c  -> Just $ a + c

instance (Eq a, Num a) => Num (Multilinear a) where
  (+) = add
  (*) = mult
  negate p = p { terms = Map.map negate (terms p) }
  abs    p = p { terms = Map.map abs (terms p) }
  signum p = p
  fromInteger _ = zero

{- Substitutions -}

-- Rename some variables
-- NOTE: Doesn't check for overlap
rename :: (Eq a, Num a) => Map String String -> Multilinear a -> Multilinear a
rename sub p = simplify $ Multilinear terms'
  where terms' = Map.mapKeys (mapMonomial (sub!)) $ terms p

renameMonotonic :: (Eq a, Num a) => Map String String -> Multilinear a -> Multilinear a
renameMonotonic sub p = simplify $ Multilinear terms'
  where terms' = Map.mapKeysMonotonic (mapMonomial (sub!)) $ terms p

-- Substitute a variable with a Boolean expression
subst :: (Eq a, Num a) => String -> Multilinear Bool -> Multilinear a -> Multilinear a
subst v exp (Multilinear terms) = simplify $ Map.foldlWithKey' f zero terms
  where f p' m a
          | v `inMonomial` m = p' + (distribute a $ ofTermDirect True (reduceMonomial v m) * exp)
          | otherwise        = p' + (ofTermDirect a m)

-- Simultaneous substitution
substMany :: (Eq a, Num a) => Map String (Multilinear Bool) -> Multilinear a -> Multilinear a
substMany sub p@(Multilinear terms) = simplify $ Map.foldlWithKey' f zero terms
  where f p' m a = p' + (distribute a $ foldl' (*) one (map g $ monomialVars m))
        g v      = Map.findWithDefault (ofVar v) v sub

-- Get possible variable substitutions giving p = 0
solveForX :: (Eq a, Fractional a) => Multilinear a -> [(String, Multilinear a)]
solveForX p = mapMaybe f . Map.toAscList . terms . simplify $ p
  where f (m, a) =
          let v  = firstVar m 
              p' = simplify $ p - ofTermDirect a m
          in
            if monomialDegree m == 1 && not (appearsIn v p')
            then Just (v, scale (recip a) p')
            else Nothing

{- Transformations -}

simplify :: (Eq a, Num a) => Multilinear a -> Multilinear a
simplify p = p { terms = Map.filter (fromInteger 0 /=) $ terms p }

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

distributeM :: (Eq a, Num a) => a -> [Monomial] -> Multilinear a
distributeM a [] = zero
distributeM a (m:xs)
  | a == fromInteger 0 = zero
  | otherwise          = p + (distributeM a xs) + distributeM (a * fromInteger (-2)) (mmult m xs)
  where p = Multilinear $ Map.singleton m a
        mmult m = map (multMonomial m)

distribute :: (Eq a, Num a) => a -> Multilinear Bool -> Multilinear a
distribute a p = distributeM a (Map.keys $ Map.filter id $ terms p)

convert :: (a -> b) -> Multilinear a -> Multilinear b
convert f p = p { terms = Map.map f $ terms p }

convertMaybe :: (a -> Maybe b) -> Multilinear a -> Maybe (Multilinear b)
convertMaybe f p = mapM f (terms p) >>= \terms' -> return $ p { terms = terms' }

{- Debug -}

{- Tests -}
p1 = ofTerm 2 ["x"]
p2 = ofTerm 3 ["y"]
p3 = ofTerm 7 ["x","y","z"]
p4 = zero
p5 = ofTerm 0 ["z"]

x0 = ofVar "x0" :: Multilinear Bool
x1 = ofVar "x1" :: Multilinear Bool
x2 = ofVar "x2" :: Multilinear Bool
x3 = ofVar "x3" :: Multilinear Bool
