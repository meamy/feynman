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
  Cyclotomic,
  var,
  constant,
  (*|),
  primitiveRoot,
  evaluate
  )
where

import Data.List
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Complex
import Data.Maybe(maybe)

import qualified Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial

{-------------------------------
 Univariate polynomials
 -------------------------------}

-- | Univariate polynomials over the ring 'r'
data Univariate r = Univariate { getCoeffs :: !(Map Integer r) } deriving (Eq, Ord)

instance (Eq r, Num r, Show r) => Show (Univariate r) where
  show = showWithName "x"

instance Degree (Univariate r) where
  degree = maybe 0 (fromIntegral . fst) . Map.lookupMax . getCoeffs

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

-- | Normalize a univariate polynomial
normalize :: (Eq r, Num r) => Univariate r -> Univariate r
normalize = Univariate . Map.filter (/=0) . getCoeffs

-- | The unique univariate variable
var :: Num r => Univariate r
var = Univariate $ Map.singleton 1 1

-- | Constant polynomial
constant :: (Eq r, Num r) => r -> Univariate r
constant a
  | a == 0    = Univariate $ Map.empty
  | otherwise = Univariate $ Map.singleton 0 a

-- | Multiply by a scalar
(*|) :: (Eq r, Num r) => r -> Univariate r -> Univariate r
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

instance Degree (Cyclotomic r) where
  degree = degree . getPoly

instance (Eq r, Num r) => Num (Cyclotomic r) where
  p + q = reduceOrder $ Cyc m (p' + q')
    where (Cyc m p', Cyc _ q') = unifyOrder p q
  p * q = reduceOrder $ Cyc m (p' * q')
    where (Cyc m p', Cyc _ q') = unifyOrder p q
  negate (Cyc m p) = Cyc m $ negate p
  abs    p = p
  signum p = p
  fromInteger i = Cyc 1 (fromInteger i)

-- | Unify the order of two cyclotomics
unifyOrder :: Cyclotomic r -> Cyclotomic r -> (Cyclotomic r, Cyclotomic r)
unifyOrder (Cyc n p) (Cyc m q)
  | n == m    = (Cyc n p, Cyc m q)
  | otherwise = (Cyc r p', Cyc r q')
  where r  = lcm n m
        p' = Univariate . Map.mapKeysMonotonic ((r `div` n) *) $ getCoeffs p
        q' = Univariate . Map.mapKeysMonotonic ((r `div` m) *) $ getCoeffs q

-- | Rewrite the cyclotomic in lowest order
reduceOrder :: (Eq r, Num r) => Cyclotomic r -> Cyclotomic r
reduceOrder (Cyc m c) = Cyc m' c'
  where m' = m `div` d
        c' = Univariate . Map.mapKeysMonotonic (`div` d) $ getCoeffs c
        d  = foldr gcd m . Map.keys $ getCoeffs c

-- | Construct the cyclotomic polynomial \(\zeta_i\)
primitiveRoot :: Num r => Integer -> Cyclotomic r
primitiveRoot i = Cyc i var

-- | Convert to a complex number
evaluate :: (Real r, RealFloat f) => Cyclotomic r -> Complex f
evaluate (Cyc m p) = Map.foldrWithKey f (0.0 :+ 0.0) $ getCoeffs p
  where f root coeff = (mkPolar (realToFrac coeff) (expnt root) +)
        expnt root   = 2.0*pi*(fromInteger root)/(fromInteger m)
