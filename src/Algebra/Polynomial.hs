module Algebra.Polynomial where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Bimap (Bimap, (!), (!>))
import qualified Data.Bimap as Bimap

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

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
type Monomial = IntSet

monomial :: [Int] -> Monomial
monomial = IntSet.fromList

monomialVars :: Monomial -> [Int]
monomialVars = IntSet.elems

monomialDegree :: Monomial -> Int
monomialDegree = IntSet.size

inMonomial :: Int -> Monomial -> Bool
inMonomial = IntSet.member

multMonomial :: Monomial -> Monomial -> Monomial
multMonomial = IntSet.union

mapMonomial :: (Int -> Int) -> Monomial -> Monomial
mapMonomial = IntSet.map

{- Multi-linear polynomials -}
data Multilinear a = Multilinear {
  vars  :: !(Bimap String Int),
  terms :: !(Map Monomial a)
  } deriving (Eq)

instance (Eq a, Num a, Show a) => Show (Multilinear a) where
  show p@(Multilinear vars terms)
    | isZero p    = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs terms)
    where showTerm (m, a)
            | monomialDegree m == 0 = show a
            | a == fromInteger 0    = show a
            | a == fromInteger 1    = showMono m
            | otherwise             = (show a) ++ (showMono m)
          showMono = concatMap (vars!>) . monomialVars

degree :: (Eq a, Num a) => Multilinear a -> Int
degree p
  | isZero p    = -1
  | otherwise = maximum $ map degTerm $ Map.toList $ terms p
  where degTerm (m, k) = if k == fromInteger 0 then -1 else monomialDegree m

coefficients :: Multilinear a -> [a]
coefficients = Map.elems . terms

{- Tests -}

isZero :: Multilinear a -> Bool
isZero = Map.null . terms

isMono :: Multilinear a -> Bool
isMono = (1 >=) . Map.size . terms

appearsIn :: String -> Multilinear a -> Bool
appearsIn v (Multilinear vars terms) = any (vars!v `inMonomial`) . Map.keys $ terms

{- Constructors -}
zero :: Multilinear a
zero = Multilinear Bimap.empty Map.empty

one :: Num a => Multilinear a
one = constant $ fromInteger 1

constant :: Num a => a -> Multilinear a
constant a = Multilinear (Bimap.empty) $ Map.singleton (monomial []) a

ofTerm :: (Eq a, Num a) => a -> [String] -> Multilinear a
ofTerm a xs
  | a == fromInteger 0 = zero
  | otherwise          = Multilinear vars $ Map.singleton (monomial [0..length xs - 1]) a
  where vars = Bimap.fromAscPairList $ zip (sort xs) [0..]

ofVar :: (Eq a, Num a) => String -> Multilinear a
ofVar v = ofTerm (fromInteger 1) [v]

ofMonomial :: (Eq a, Num a) => [String] -> Multilinear a
ofMonomial xs = ofTerm (fromInteger 1) xs

{- Operators -}

scale :: (Eq a, Num a) => a -> Multilinear a -> Multilinear a
scale a p
  | a == fromInteger 0 = zero
  | otherwise          = p { terms = Map.map (a *) $ terms p }

unsafeAdd :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
unsafeAdd p q = Multilinear (vars p) $ Map.unionWith (+) (terms p) (terms q)

unsafeMult :: (Eq a, Num a) => Multilinear a -> Multilinear a -> Multilinear a
unsafeMult p q = Map.foldlWithKey' f init (terms p)
    where init              = zero { vars = vars p }
          f acc m a         =
            let amq = Multilinear (vars p) (Map.foldlWithKey' (g m a) Map.empty (terms q)) in
              unsafeAdd acc amq
          g m a terms m' a' = Map.alter (h $ a * a') (multMonomial m m') terms
          h a b             = case b of
            Nothing -> Just a
            Just c  -> Just $ a + c

instance (Eq a, Num a) => Num (Multilinear a) where
  p + q = (uncurry unsafeAdd) $ unifyFrame p q
  p * q = (uncurry unsafeMult) $ unifyFrame p q
  negate p = p { terms = Map.map negate (terms p) }
  abs    p = p { terms = Map.map abs (terms p) }
  signum p = p
  fromInteger _ = zero

{- Substitutions -}

renameMonotonic :: Map String String -> Multilinear a -> Multilinear a
renameMonotonic sub p = Multilinear vars' terms'
  where vars'  = Bimap.mapMonotonic (\v -> Map.findWithDefault v v sub) $ vars p
        terms' = Map.mapKeys (mapMonomial $ \i -> vars'!((vars p)!>i)) $ terms p

{-
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
getSubst p = case (break f $ Map.toDescList $ terms $ simplify p) of
  (terms, [])            -> Nothing
  (terms, (m, a):terms') -> Just (firstVar m, scale (recip a) $ p { terms = Map.fromDescList $ terms ++ terms' })
  where f (m, a) =
          let i = firstVar m in
            degMon m == 1 && not (appearsIn i (simplify $ p - ofTerm a [i]))
-}

{- Transformations -}

{-
-- WARNING: sub must be monotonic & must obey k > k' => v > v' for all pairs (k, v), (k', v') in sub
reindex :: Map Int Int -> Multilinear a -> Multilinear a
reindex sub = ofMultilinear sub (n + 1)
  where n = case Map.lookupMax sub of
              Nothing     -> 0
              Just (_, v) -> v

simplify :: (Eq a, Num a) => Multilinear a -> Multilinear a
simplify p = p { terms = Map.filter (fromInteger 0 /=) $ terms p }

addVars :: Int -> Int -> Multilinear a -> Multilinear a
addVars n i p@(Multilinear v terms)
  | n <= 0    = p
  | otherwise = Multilinear (v + n) (Map.mapKeysMonotonic shiftAbove terms)
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
-}

{- Internal -}

-- Merges two variable maps, producing a new variable map and a substitution
-- map for the second input
mergeVars :: Bimap String Int -> Bimap String Int -> (Bimap String Int, Map Int Int)
mergeVars vars vars' =
  let maxVar              = 1 + fst (Bimap.findMaxR vars)
      (vars'', sub, _)    = Bimap.fold f (vars, Map.empty, maxVar) vars'
      f v i (acc, sub, j) = case (Bimap.lookup v acc, Bimap.lookupR i acc) of
          (Just i', _)
            | i == i'   -> (acc, sub, j)
            | otherwise -> (acc, Map.insert i i' sub, j)
          (_, Nothing)  -> (Bimap.insert v i acc, sub, j)
          (_, Just _)   -> (Bimap.insert v j acc, Map.insert i j sub, j+1)
  in
    (vars'', sub)

unifyFrame :: Multilinear a -> Multilinear a -> (Multilinear a, Multilinear a)
unifyFrame p q =
  let (vars', sub) = mergeVars (vars p) (vars q)
      p'           = p { vars = vars' }
      q'           =
        let subst i = Map.findWithDefault i i sub in
          q { vars = vars',
              terms = Map.mapKeys (IntSet.map subst) $ terms q }
  in
    (p', q')
    
-- Repacks a multilinear polynomial

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
