{-|
Module      : Univariate
Description : Univariate polynomials (notably cyclotomics)
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Polynomial.Univariate(
  Univariate,
  var,
  constant,
  (*|)
  )
where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Complex

import qualified Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base

{-------------------------------
 Univariate polynomials
 -------------------------------}

-- | Univariate polynomials over the ring 'r'
data Univariate r = Univariate { getCoeffs :: !(Map Integer r) } deriving (Eq, Ord)

instance (Eq r, Num r, Show r) => Show (Univariate r) where
  show = showWithName "x"

-- | Print a univariate polynomial with a particular variable name
showWithName :: (Eq r, Num r, Show r) => String -> Univariate r -> String
showWithName x p
    | p == 0    = "0"
    | otherwise = intercalate " + " $ map showTerm (Map.assocs $ getCoeffs p)
    where showTerm (expt, a)
            | expt == 0  = show a
            | a    == 1  = showExpt expt
            | a    == -1 = "-" ++ showExpt expt
            | otherwise  = show a ++ showExpt expt
          showExpt expt
            | expt == 1  = x
            | otherwise  = Unicode.sup x expt

instance (Eq r, Num r) => Num (Univariate r) where
  (+)           = add
  (*)           = mult
  negate        = Univariate . Map.map negate . getCoeffs
  abs           = id
  signum        = id
  fromInteger 0 = Univariate Map.empty
  fromInteger i = Univariate $ Map.singleton 0 (fromInteger i)

instance (Eq r, Abelian r) => Abelian (Univariate r) where
  zero    = Univariate Map.empty
  power i = Univariate . Map.map (power i) . getCoeffs
  order _ = 0

instance (Eq r, Ring r) => Ring (Univariate r) where
  one = Univariate $ Map.singleton 0 1

-- | Normalize a univariate polynomial
normalize :: (Eq r, Num r) => Univariate r -> Univariate r
normalize = Univariate . Map.filter (/=0) . getCoeffs

-- | The unique univariate variable
var :: Ring r => Univariate r
var = Univariate $ Map.singleton 1 1

-- | Constant polynomial
constant :: (Eq r, Ring r) => r -> Univariate r
constant a
  | a == 0    = Univariate $ Map.empty
  | otherwise = Univariate $ Map.singleton 0 a

-- | Multiply by a scalar
(*|) :: (Eq r, Ring r) => r -> Univariate r -> Univariate r
(*|) 0 = \_p -> zero
(*|) a = Univariate . Map.map (a*) . getCoeffs

-- | Add two univariate polynomials
add :: (Eq r, Num r) => Univariate r -> Univariate r -> Univariate r
add p = normalize . Univariate . Map.unionWith (+) (getCoeffs p) . getCoeffs

-- | Multiply two univariate polynomials
mult :: (Eq r, Num r) => Univariate r -> Univariate r -> Univariate r
mult p = normalize . Map.foldrWithKey (\expt a -> add (mulTerm expt a)) 0 . getCoeffs
  where mulTerm expt a = Univariate . Map.mapKeysMonotonic (+ expt) . Map.map (* a) $ getCoeffs p

{-------------------------------
 Cyclotomics
 -------------------------------}
-- | Cyclotomic polynomials over the ring 'r'
data Cyclotomic r = Cyc { getOrder :: !Integer, getPoly :: !(Univariate r) } deriving (Eq, Ord)

instance (Eq r, Num r, Show r) => Show (Cyclotomic r) where
  show p = showWithName (Unicode.sub Unicode.zeta (getOrder p)) $ getPoly p

instance (Eq r, Num r) => Num (Cyclotomic r) where
  p + q = reduceOrder $ Cyc m (p' + q')
    where (Cyc m p', Cyc _ q') = unify p q
  p * q = reduceOrder $ Cyc m (p' * q')
    where (Cyc m p', Cyc _ q') = unify p q
  negate (Cyc m p) = Cyc m $ negate p
  abs    p = p
  signum p = p
  fromInteger i = Cyc 1 (fromInteger i)

-- | Unify the order of two cyclotomics
unify :: Cyclotomic r -> Cyclotomic r -> (Cyclotomic r, Cyclotomic r)
unify p q = case compare n m of
  Eq -> (p, q)
  Lt -> (Cyc m (Map.mayKeysMonotonic (+ (m-n)) $ getPoly p), q)
  Gt -> (p, Cyc n (Map.mayKeysMonotonic (+ (n-m)) $ getPoly q))
  where n = getOrder p
        m = getOrder q

-- | Rewrite the cyclotomic in lowest order
reduceOrder :: (Eq r, Num r) => Cyclotomic r -> Cyclotomic r
reduceOrder (Cyc m c) = Cyc m' c'
  where m' = m `div` d
        c' = Map.mapKeysMonotonic (`div` d) c
        d  = foldr gcd m $ Map.keys c

-- | Construct the cyclotomic polynomial \(\zeta_i\)
primitiveRoot :: Num r => Integer -> Cyclotomic r
primitiveRoot i = Cyc i var

-- | Add two cyclotomic polynomials
add :: (Eq r, Num r) => Cyclotomic r -> Cyclotomic r -> Cyclotomic r
add p q
  | ord p == ord q = normalize $ Cyc (ord p) (Map.unionWith (+) (coeffs p) (coeffs q))
  | otherwise          = add p' q'
  where p' = Cyc m' $ Map.mapKeysMonotonic ((m' `div` (ord p)) *) (coeffs p)
        q' = Cyc m' $ Map.mapKeysMonotonic ((m' `div` (ord q)) *) (coeffs q)
        m' = lcm (ord p) (ord q)

-- | Multiply two cyclotomic polynomials
mult :: (Eq r, Num r) => Cyclotomic r -> Cyclotomic r -> Cyclotomic r
mult p q = normalize $ Map.foldrWithKey f zero $ coeffs p
  where f root coeff = add (Cyc ord' $ Map.foldrWithKey (g root coeff) Map.empty (coeffs q))
        g r c r' c'  = Map.alter (addCoeff $ c * c') ((r*multP + r'*multQ) `mod` ord')
        ord'         = lcm (ord p) (ord q)
        multP        = ord' `div` (ord p)
        multQ        = ord' `div` (ord q)
        addCoeff a b = case b of
          Nothing -> Just a
          Just c  -> Just $ a + c

-- | Convert to a complex number
toComplex :: (Real r, RealFloat f) => Cyclotomic r -> Complex f
toComplex p = Map.foldrWithKey f (0.0 :+ 0.0) $ coeffs p
  where f root coeff = (mkPolar (realToFrac coeff) (expnt root) +)
        expnt root   = 2.0*pi*(fromInteger root)/(fromInteger $ ord p)
-}
