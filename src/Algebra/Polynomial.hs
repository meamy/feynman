module Algebra.Polynomial where

import Data.Map (Map, (!))
import qualified Data.Map as Map

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
type Monomial = Integer

bits :: (Bits a) => [Int] -> a
bits = foldl' (\m i -> m .|. bit i) zeroBits

bitSet :: (Bits a) => Int -> a -> [Int]
bitSet n m = mapMaybe (\i -> if testBit m i then Just i else Nothing) [0..n-1]

degMon :: Monomial -> Int
degMon = popCount


-- WARNING: Can loop infinitely if popCount < 1
firstVar :: Monomial -> Int
firstVar m = fromJust $ findIndex (testBit m) [0..]

{- Multi-linear polynomials -}
data Multilinear a = Multilinear {
  vars  :: !Int,
  terms :: !(Map Monomial a)
  } deriving (Eq)

instance (Eq a, Num a, Show a) => Show (Multilinear a) where
  show p@(Multilinear n terms)
    | isZero p    = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs terms)
    where showTerm (m, a)
            | a == fromInteger 0 = "0"
            | a == fromInteger 1 = showMono m
            | otherwise          = (show a) ++ "*" ++ (showMono m)
          showMono m = concatMap (\i -> if testBit m i then "x" ++ show i else "") [0..n-1]

deg :: (Eq a, Num a) => Multilinear a -> Int
deg p
  | isZero p    = -1
  | otherwise = maximum $ map degTerm $ Map.toList $ terms p
  where degTerm (m, k) = if k == fromInteger 0 then -1 else degMon m

coeffs :: Multilinear a -> [a]
coeffs = Map.elems . terms

{- Tests -}

isZero :: Multilinear a -> Bool
isZero = Map.null . terms

isMono :: Multilinear a -> Bool
isMono = (1 >=) . Map.size . terms

appearsIn :: Int -> Multilinear a -> Bool
appearsIn i = any (flip testBit $ i) . Map.keys . terms

{- Constructors -}
zero :: Multilinear a
zero = Multilinear 0 Map.empty

one :: Num a => Multilinear a
one = Multilinear 0 $ Map.singleton 0 (fromInteger 1)

constant :: Num a => a -> Multilinear a
constant a = Multilinear 0 $ Map.singleton 0 a

ofTerm :: (Eq a, Num a) => a -> [Int] -> Multilinear a
ofTerm a xs
  | a == fromInteger 0 = zero
  | otherwise          = Multilinear (maximum xs + 1) $ Map.singleton (bits xs) a

ofTermDirect :: (Eq a, Num a) => Int -> a -> Monomial -> Multilinear a
ofTermDirect n a m
  | a == fromInteger 0 = zero
  | otherwise          = Multilinear n $ Map.singleton m a

ofVar :: (Eq a, Num a) => Int -> Multilinear a
ofVar i = ofTerm (fromInteger 1) [i]

{- Operators -}

scale :: (Eq a, Num a) => a -> Multilinear a -> Multilinear a
scale a p
  | a == fromInteger 0 = zero
  | otherwise          = p { terms = Map.map (a *) $ terms p }

add :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
add p q = Multilinear (max (vars p) (vars q)) $ Map.unionWith (+) (terms p) (terms q)

mult :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
mult p q = Map.foldlWithKey' f zero (terms p)
    where f poly m a        = (+) poly $ q { terms = Map.foldlWithKey' (g m a) Map.empty (terms q) }
          g m a terms m' a' = Map.insert (m .|. m') (a * a') terms

instance (Eq a, Num a) => Num (Multilinear a) where
  (+) = add
  (*) = mult
  negate p = p { terms = Map.map negate (terms p) }
  abs    p = p { terms = Map.map abs (terms p) }
  signum p = p
  fromInteger _ = zero

{- Substitutions -}

-- Substitution assumes all variables in the substitution are already tracked
subst :: (Eq a, Num a) => Int -> Multilinear Bool -> Multilinear a -> Multilinear a
subst i sub (Multilinear n terms) = Map.foldlWithKey' f zero terms
  where f p' m a
          | testBit m i = p' + (distribute n a $ ofTermDirect n True (clearBit m i) * sub)
          | otherwise   = p' + (ofTermDirect n a m)

-- WARNING: sub must map all variables of p to polynomials
substAll :: (Eq a, Num a) => Map Int (Multilinear Bool) -> Multilinear a -> Multilinear a
substAll sub p@(Multilinear n terms) = Map.foldlWithKey' f zero terms
  where f p' m a = p' + (distribute n a $ foldl' (*) one (map (sub !) $ bitSet n m))

substMany :: (Eq a, Num a) => Map Int (Multilinear Bool) -> Multilinear a -> Multilinear a
substMany sub p@(Multilinear n terms) = Map.foldlWithKey' f zero terms
  where f p' m a = p' + (distribute n' a $ foldl' (*) one (map g $ bitSet n m))
        g i      = Map.findWithDefault (ofVar i) i sub
        n'       = maximum $ [n] ++ (map vars $ Map.elems sub)

-- Pick a substitution, if possible, for a variable assuming p = 0. Favours higher variables indices
-- Note that simplification is crucial here
getSubst :: (Eq a, Fractional a) => Multilinear a -> Maybe (Int, Multilinear a)
getSubst p = case (break (\(m, _) -> degMon m == 1) $ Map.toDescList $ terms $ simplify p) of
  (terms, [])            -> Nothing
  (terms, (m, a):terms') -> Just (firstVar m, scale (recip a) $ p { terms = Map.fromDescList $ terms ++ terms' })

{- Transformations -}
simplify :: (Eq a, Num a) => Multilinear a -> Multilinear a
simplify p = p { terms = Map.filter (fromInteger 0 /=) $ terms p }

addVars :: Int -> Int -> Multilinear a -> Multilinear a
addVars n i (Multilinear v terms) = Multilinear (v + n) (Map.mapKeysMonotonic shiftAbove terms)
  where shiftAbove m = let mask = m .&. (bit i - 1) in
          mask .|. (shiftL (m .&. complement mask) n)

factorOut :: Int -> Multilinear a -> Multilinear a
factorOut i p = p { terms = terms' }
  where terms' = Map.mapKeysMonotonic (flip clearBit i) . Map.filterWithKey (\m _ -> testBit m i) $ terms p

removeVar :: Int -> Multilinear a -> Multilinear a
removeVar i p = p { terms = terms' }
  where terms' = Map.filterWithKey (\m _ -> not $ testBit m i) $ terms p

distributeM :: (Eq a, Num a) => Int -> a -> [Monomial] -> Multilinear a
distributeM n a [] = zero
distributeM n a (m:xs)
  | a == fromInteger 0 = zero
  | otherwise          = p + (distributeM n a xs) + distributeM n (a * fromInteger (-2)) (mmult m xs)
  where p = Multilinear n $ Map.singleton m a
        mmult m = map (m .|.)

distribute :: (Eq a, Num a) => Int -> a -> Multilinear Bool -> Multilinear a
distribute n a p = distributeM n a (Map.keys $ Map.filter id $ terms p)

convert :: (a -> b) -> Multilinear a -> Multilinear b
convert f p = p { terms = Map.map f $ terms p }

convertMaybe :: (a -> Maybe b) -> Multilinear a -> Maybe (Multilinear b)
convertMaybe f p = mapM f (terms p) >>= \terms' -> return $ p { terms = terms' }

{- Debug -}

{- Tests -}
p1 = ofTerm 2 [0]
p2 = ofTerm 3 [1]
p3 = ofTerm 7 [0,1,3]
p4 = zero
p5 = ofTerm 0 [3]

x0 = ofVar 0 :: Multilinear Bool
x1 = ofVar 1 :: Multilinear Bool
x2 = ofVar 2 :: Multilinear Bool
x3 = ofVar 3 :: Multilinear Bool
