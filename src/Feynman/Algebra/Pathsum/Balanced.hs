{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE Rank2Types #-}

{-|
Module      : Balanced
Description : Amplitude-balanced path sums
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Pathsum.Balanced where

import Data.List
import qualified Data.Set as Set
import Data.Ratio
import Data.Semigroup
import Control.Monad (mzero, msum)
import Data.Maybe (maybeToList)
import Data.Complex (Complex, mkPolar)
import Data.Bits (shiftL)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.String (IsString(..))
import Data.Tuple (swap)
import Data.Functor.Identity

import qualified Feynman.Util.Unicode as U
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial (degree)
import Feynman.Algebra.Polynomial.Multilinear

{-----------------------------------
 Variables
 -----------------------------------}

-- | Variables are either input variables or path variables. The distinction
--   is due to the binding structure of our pathsum representation, and moreover
--   improves readability
data Var = IVar !Int | PVar !Int | FVar !String deriving (Eq, Ord)

instance Show Var where
  show (IVar i) = U.sub "x" $ fromIntegral i
  show (PVar i) = U.sub "y" $ fromIntegral i
  show (FVar x) = x

instance IsString Var where
  fromString = FVar

instance Ord (Monomial Var repr) where
  compare = lexOrd

-- | Convenience function for the string representation of the 'i'th input variable
ivar :: Int -> String
ivar = show . IVar

-- | Convenience function for the string representation of the 'i'th path variable
pvar :: Int -> String
pvar = show . PVar

-- | Construct an integer shift for input variables
shiftI :: Int -> (Var -> Var)
shiftI i = shiftAll i 0

-- | Construct an integer shift for path variables
shiftP :: Int -> (Var -> Var)
shiftP j = shiftAll 0 j

-- | General shift. Constructs a substitution from shift values for I and P
shiftAll :: Int -> Int -> (Var -> Var)
shiftAll i j = go
  where go (IVar i') = IVar (i + i')
        go (PVar j') = PVar (j + j')

-- | Check if a variable is an input
isI :: Var -> Bool
isI (IVar _) = True
isI _        = False

-- | Check if a variable is a path variable
isP :: Var -> Bool
isP (PVar _) = True
isP _        = False

-- | Check if a variable is a free variable
isF :: Var -> Bool
isF (FVar _) = True
isF _        = False

-- | Get the string of a free variable
unF :: Var -> String
unF (FVar s) = s
unF _        = error "Not a free variable"

{-----------------------------------
 Path sums
 -----------------------------------}

-- | Path sums of the form
--   \(\frac{1}{\sqrt{2}^k}\sum_{y\in\mathbb{Z}_2^m}e^{i\pi P(x, y)}|f(x, y)\rangle\)
data Pathsum g = Pathsum {
  sde       :: !Int,
  inDeg     :: !Int,
  outDeg    :: !Int,
  pathVars  :: !Int,
  phasePoly :: !(PseudoBoolean Var g),
  outVals   :: ![SBool Var]
  } deriving (Eq)

instance (Show g, Eq g, Periodic g, Real g) => Show (Pathsum g) where
  show sop = inputstr ++ scalarstr ++ sumstr ++ amplitudestr ++ statestr
    where inputstr = case inDeg sop of
            0 -> ""
            1 -> U.ket (ivar 0) ++ " " ++ U.mapsto ++ " "
            2 -> U.ket (ivar 0) ++ U.ket (ivar 1) ++ " " ++ U.mapsto ++ " "
            j -> U.ket (ivar 0) ++ U.dots ++ U.ket (ivar (j-1)) ++ " " ++ U.mapsto ++ " "
          scalarstr = case compare (sde sop) 0 of
            LT -> U.sup ("(" ++ U.rt2 ++ ")") (fromIntegral . abs $ sde sop)
            EQ -> if (inDeg sop == 0 && outDeg sop == 0 && phasePoly sop == 0) then "1" else ""
            GT -> U.sup ("1/(" ++ U.rt2 ++ ")") (fromIntegral $ sde sop)
          sumstr = case pathVars sop of
            0 -> ""
            1 -> U.sum ++ "[" ++ pvar 0 ++ "]"
            2 -> U.sum ++ "[" ++ pvar 0 ++ pvar 1 ++ "]"
            j -> U.sum ++ "[" ++ pvar 0 ++ U.dots ++ pvar (j-1) ++ "]"
          amplitudestr = case order (phasePoly sop) of
            0 -> U.e ++ "^" ++ U.i ++ U.pi ++ "{" ++ show (phasePoly sop) ++ "}"
            1 -> ""
            2 -> "(-1)^{" ++ show (makeIntegral 1 $ phasePoly sop) ++ "}"
            4 -> U.i ++ "^{" ++ show (makeIntegral 2 $ phasePoly sop) ++ "}"
            8 -> U.omega ++ "^{" ++ show (makeIntegral 4 $ phasePoly sop) ++ "}"
            j -> U.sub U.zeta j ++ "^{" ++ show (makeIntegral j $ phasePoly sop) ++ "}"
          statestr = concatMap (U.ket . show) $ outVals sop

-- | Convenience function for pretty printing
makeIntegral :: Real g => Integer -> PseudoBoolean v g -> PseudoBoolean v Integer
makeIntegral i = cast (\a -> numerator $ toRational a * toRational i)

-- | Retrieve the internal path variables
internalPaths :: Pathsum g -> [Var]
internalPaths sop = [PVar i | i <- [0..pathVars sop - 1]] \\ outVars
  where outVars = Set.toList . Set.unions . map vars $ outVals sop

-- | Retrieve the free variables
freeVars :: Pathsum g -> [String]
freeVars sop = map unF . Set.toList . Set.filter isF . foldr (Set.union) Set.empty $ xs
  where xs = (vars $ phasePoly sop):(map vars $ outVals sop)

-- | Checks if the path sum is (trivially) the identity
isTrivial :: (Eq g, Num g) => Pathsum g -> Bool
isTrivial sop = sop == identity (inDeg sop)

-- | (To be deprecated) Drops constant term from the phase polynomial
dropGlobalPhase :: (Eq g, Num g) => Pathsum g -> Pathsum g
dropGlobalPhase sop = sop { phasePoly = dropConstant $ phasePoly sop }

-- | (To be deprecated) Drops the phase polynomial
dropPhase :: (Eq g, Num g) => Pathsum g -> Pathsum g
dropPhase sop = sop { phasePoly = 0 }

-- | (To be deprecated) Drops normalization
dropAmplitude :: Pathsum g -> Pathsum g
dropAmplitude sop = sop { sde = 0 }

-- | (For debugging) Returns the number of terms in a path sum
numTerms :: Pathsum g -> Int
numTerms sop = foldl' (+) (countTerms $ phasePoly sop) [countTerms f | f <- outVals sop]
  where countTerms = length . toTermList

{-----------------------------------
 Lenses
 -----------------------------------}

-- | The type of lenses. Coincides with the lens library definition
type Lens a b = forall f. Functor f => (b -> f b) -> a -> f a

-- | Lens for lists
ix :: Int -> Lens [a] a
ix i f xs = fmap go $ f (xs!!i) where
  go a = map (\(b,j) -> if j == i then a else b) (zip xs [0..])

-- | Lens for the output state
state :: Lens (Pathsum g) [SBool Var]
state f sop = fmap go $ f (outVals sop) where
  go vals = sop { outVals = vals }

-- | Setter over a lens. Coincides with the lens library function
over :: Lens a b -> (b -> b) -> a -> a
over lens f a = runIdentity $ (lens $ Identity . f) a

-- | Set a value at a point over a lens
set :: Lens a b -> b -> a -> a
set lens b = over lens (const b)

{----------------------------
 Constructors
 ----------------------------}

-- | Construct an 'n'-qubit identity operator
identity :: (Eq g, Num g) => Int -> Pathsum g
identity n = Pathsum 0 n n 0 0 [ofVar (IVar i) | i <- [0..n-1]]

-- | Construct a (symbolic) state
ket :: (Eq g, Num g) => [SBool String] -> Pathsum g
ket xs = Pathsum 0 0 (fromIntegral $ length xs) 0 0 $ map (rename FVar) xs

-- | Initialize a fresh ancilla
initialize :: (Eq g, Num g) => FF2 -> Pathsum g
initialize b = ket [constant b]

{-# INLINE initialize #-}

-- | Construct a uniform superposition of classical states of a given form
superposition :: (Eq g, Num g) => [SBool String] -> Pathsum g
superposition xs = Pathsum k 0 n k 0 $ map (rename sub) xs
  where n   = length xs
        k   = Set.size fv
        fv  = Set.unions $ map vars xs
        sub = ((Map.fromList [(v, PVar i) | (v, i) <- zip (Set.toList fv) [0..]])!)

-- | Construct a classical transformation from the free variables of 'xs' to 'xs'
--   Effectively binds the free variables in 'state xs'
compute :: (Eq g, Num g) => [SBool String] -> Pathsum g
compute xs = Pathsum 0 (Set.size fv) (length xs) 0 0 $ map (rename sub) xs
  where fv  = Set.unions $ map vars xs
        sub = ((Map.fromList [(v, IVar i) | (v, i) <- zip (Set.toList fv) [0..]])!)

-- | Breaks the connection between inputs and outputs by mapping
--   any input basis state to the maximally mixed state. Non-unitary
disconnect :: (Eq g, Num g) => Int -> Pathsum g
disconnect n = Pathsum n n n n 0 [ofVar $ PVar i | i <- [0..n-1]]

-- | Construct a permutation
permutation :: (Eq g, Num g) => [Int] -> Pathsum g
permutation xs
  | all (\i -> i >= 0 && i <= n) xs = Pathsum 0 n n 0 0 (map (ofVar . IVar) xs)
  | otherwise = error "permutation: Input not a permutation"
  where n = length xs

-- | Construct an n-ary unit
etaN :: (Eq g, Num g) => Int -> Pathsum g
etaN n = Pathsum 0 0 (2*n) n 0 $ xs ++ xs
  where xs = map (ofVar . PVar) [0..n-1]

{----------------------------
 Dual constructors
 ----------------------------}

-- | Construct a (symbolic) state destructor
bra :: (Eq g, Abelian g) => [SBool String] -> Pathsum g
bra xs = Pathsum (2*m) m 0 m (lift $ p) []
  where m         = fromIntegral $ length xs
        p         = foldr (+) 0 . map go $ zip [0..] xs
        go (i, v) = ofVar (PVar i) * (ofVar (IVar i) + (rename fromString v))

-- | Alternate state destructor with fewer paths but a more complicated polynomial
unstateAlt :: (Eq g, Abelian g) => [SBool String] -> Pathsum g
unstateAlt xs = Pathsum 2 (fromIntegral $ length xs) 0 1 (lift $ y*(1 + p)) []
  where y = ofVar (PVar 0)
        p = foldr (*) 1 . map valF $ zip xs [0..]
        valF (val, i) = 1 + (rename fromString val) + ofVar (IVar i)

-- | Dagger of initialize -- i.e. unnormalized post-selection
postselect :: (Eq g, Abelian g) => FF2 -> Pathsum g
postselect b = bra [constant b]

{-# INLINE postselect #-}

-- | Select on a classical state of a given form
unsuper :: (Eq g, Abelian g) => [SBool String] -> Pathsum g
unsuper xs = Pathsum (2*m + n) m 0 (m+n) poly []
  where m    = length xs
        n    = Set.size fv
        fv   = Set.unions $ map vars xs
        sub  = ((Map.fromList [(v, PVar (m + i)) | (v, i) <- zip (Set.toList fv) [0..]])!)
        poly = foldr (+) zero $ map constructTerm [0..m-1]
        constructTerm i = lift $ ofVar (PVar i) * (ofVar (IVar i) + rename sub (xs!!i))

-- | Invert a classical transformation
uncompute :: (Eq g, Abelian g) => [SBool String] -> Pathsum g
uncompute xs = Pathsum (2*m) m n (m+n) poly [ofVar (PVar $ m + i) | i <- [0..n-1]]
  where m    = length xs
        n    = Set.size fv
        fv   = Set.unions $ map vars xs
        sub  = ((Map.fromList [(v, PVar (m + i)) | (v, i) <- zip (Set.toList fv) [0..]])!)
        poly = foldr (+) zero $ map constructTerm [0..m-1]
        constructTerm i = lift $ ofVar (PVar i) * (ofVar (IVar i) + rename sub (xs!!i))

-- | Construct an inverse permutation
unpermutation :: (Eq g, Num g) => [Int] -> Pathsum g
unpermutation = permutation . snd . unzip . sort . map swap . zip [0..]

-- | Construct an n-ary co-unit
epsilonN :: (Eq g, Abelian g) => Int -> Pathsum g
epsilonN n = Pathsum (2*n) (2*n) 0 n (lift poly) []
  where poly = sum $ map f [0..n-1]
        f i  = ofVar (PVar i) * (ofVar (IVar i) + ofVar (IVar $ n+i))

{----------------------------
 Constants
 ----------------------------}

-- | \(\sqrt{2}\)
root2 :: (Eq g, Abelian g, Dyadic g) => Pathsum g
root2 = Pathsum 0 0 0 1 ((-constant (half * half)) + distribute half (ofVar (PVar 0))) []

-- | \(1/\sqrt{2}\)
roothalf :: (Eq g, Abelian g, Dyadic g) => Pathsum g
roothalf = Pathsum 1 0 0 0 0 []

-- | \(i\)
iunit :: (Eq g, Abelian g, Dyadic g) => Pathsum g
iunit = Pathsum 0 0 0 0 (constant half) []

-- | \(e^{i\pi/4}\)
omega :: (Eq g, Abelian g, Dyadic g) => Pathsum g
omega = Pathsum 0 0 0 0 (constant (half * half)) []

-- | A fresh, 0-valued ancilla
fresh :: (Eq g, Num g) => Pathsum g
fresh = Pathsum 0 0 1 0 0 [0]

-- | The dagger of fresh
unfresh :: (Eq g, Abelian g) => Pathsum g
unfresh = dagger fresh

-- | The unit, \(\eta\)
eta :: (Eq g, Num g) => Pathsum g
eta = Pathsum 0 0 2 1 0 [ofVar (PVar 0), ofVar (PVar 0)]

-- | The co-unit, \(\epsilon\)
epsilon :: (Eq g, Abelian g) => Pathsum g
epsilon = Pathsum 2 2 0 1 p []
  where p = lift $ ofVar (PVar 0) * (ofVar (IVar 0) + ofVar (IVar 1))

{----------------------------
 Matrices
 ----------------------------}

-- | X gate
xgate :: (Eq g, Num g) => Pathsum g
xgate = Pathsum 0 1 1 0 0 [1 + ofVar (IVar 0)]

-- | Z gate
zgate :: (Eq g, Abelian g) => Pathsum g
zgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = lift $ ofVar (IVar 0)

-- | Y gate
ygate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
ygate = Pathsum 0 1 1 0 p [1 + ofVar (IVar 0)]
  where p = constant half + (lift $ ofVar (IVar 0))

-- | S gate
sgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
sgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute half (ofVar (IVar 0))

-- | S* gate
sdggate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
sdggate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute (-half) (ofVar (IVar 0))

-- | T gate
tgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
tgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute (half*half) (ofVar (IVar 0))

-- | T* gate
tdggate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
tdggate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute (-half*half) (ofVar (IVar 0))

-- | R_k gate
rkgate :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g
rkgate k = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute (fromDyadic $ dyadic 1 k) (ofVar (IVar 0))

-- | R_z gate
rzgate :: (Eq g, Abelian g, Dyadic g) => g -> Pathsum g
rzgate theta = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = distribute theta (ofVar (IVar 0))

-- | H gate
hgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
hgate = Pathsum 1 1 1 1 p [ofVar (PVar 0)]
  where p = lift $ (ofVar $ IVar 0) * (ofVar $ PVar 0)

-- | CNOT gate
cxgate :: (Eq g, Num g) => Pathsum g
cxgate = Pathsum 0 2 2 0 0 [x0, x0+x1]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1

-- | CZ gate
czgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
czgate = Pathsum 0 2 2 0 p [x0, x1]
  where p = lift $ x0 * x1
        x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1

-- | Toffoli gate
ccxgate :: (Eq g, Num g) => Pathsum g
ccxgate = Pathsum 0 3 3 0 0 [x0, x1, x2 + x0*x1]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1
        x2 = ofVar $ IVar 2

-- | CCZ gate
cczgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
cczgate = Pathsum 0 3 3 0 p [x0, x1, x2]
  where p = lift $ x0 * x1 * x2
        x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1
        x2 = ofVar $ IVar 2

-- | k-control Toffoli gate
mctgate :: (Eq g, Num g) => Int -> Pathsum g
mctgate k = Pathsum 0 (k+1) (k+1) 0 0 (ctrls ++ [t + foldr (*) 1 ctrls])
  where ctrls = [ofVar (IVar i) | i <- [0..k-1]]
        t     = ofVar $ IVar k

-- | k-control Z gate
mczgate :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g
mczgate k = Pathsum 0 k k 0 p ctrls
  where ctrls = [ofVar (IVar i) | i <- [0..k-1]]
        p     = lift $ (foldr (*) 1 ctrls)

-- | n-qubit R_z gate
rzNgate :: (Eq g, Abelian g, Dyadic g) => g -> Int -> Pathsum g
rzNgate theta k = Pathsum 0 k k 0 p ctrls
  where ctrls = [ofVar (IVar i) | i <- [0..k-1]]
        p     = distribute theta (foldr (*) 1 ctrls)

-- | SWAP gate
swapgate :: (Eq g, Num g) => Pathsum g
swapgate = Pathsum 0 2 2 0 0 [x1, x0]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1

-- | CH gate
chgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
chgate = Pathsum 1 2 2 1 p [x1, x2 + x1*x2 + x1*y]
  where p = distribute (-half*half) (1 + x1) +
            distribute half (lift $ (1 + x1) * y) +
            (lift $ x1 * x2 * y)
        x1 = ofVar $ IVar 0
        x2 = ofVar $ IVar 1
        y = ofVar $ PVar 0

{----------------------------
 Applicative style
 ----------------------------}

-- | apply an X gate
applyX :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyX i (Pathsum s d o p pp ovals) = Pathsum s d o p pp ovals'
  where ovals' = over (ix i) (+ 1) ovals

-- | apply a Z gate
applyZ :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyZ i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute 1 (ovals!!i)

-- | apply a Y gate
applyY :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyY i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals'
  where ovals' = over (ix i) (+ 1) ovals
        pp'    = pp + distribute 1 (ovals!!i) + constant half

-- | apply an S gate
applyS :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyS i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute half (ovals!!i)

-- | apply an Sdg gate
applySdg :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applySdg i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute (-half) (ovals!!i)

-- | apply a T gate
applyT :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyT i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute (half*half) (ovals!!i)

-- | apply a Tdg gate
applyTdg :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyTdg i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute (-half*half) (ovals!!i)

-- | apply an Rk gate
applyRk :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyRk k i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute (fromDyadic $ dyadic 1 k) (ovals!!i)

-- | apply an Rz gate
applyRz :: (Eq g, Abelian g, Dyadic g) => g -> Int -> Pathsum g -> Pathsum g
applyRz theta i (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute (theta) (ovals!!i)

-- | apply an H gate
applyH :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyH i (Pathsum s d o p pp ovals) = Pathsum (s+1) d o (p+1) pp' ovals'
  where pp'    = pp + distribute 1 ((ovals!!i) * (ofVar $ PVar p))
        ovals' = set (ix i) (ofVar (PVar p)) ovals

-- | apply a CZ gate
applyCZ :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyCZ i j (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute 1 (ovals!!i * ovals!!j)

-- | apply a CX gate
applyCX :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyCX i j (Pathsum s d o p pp ovals) = Pathsum s d o p pp ovals' where
  ovals' = over (ix j) (+ ovals!!i) ovals

-- | apply a CCZ gate
applyCCZ :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Int -> Pathsum g -> Pathsum g
applyCCZ i j k (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals
  where pp' = pp + distribute 1 (ovals!!i * ovals!!j * ovals!!k)

-- | apply a CCX gate
applyCCX :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Int -> Pathsum g -> Pathsum g
applyCCX i j k (Pathsum s d o p pp ovals) = Pathsum s d o p pp ovals' where
  ovals' = over (ix k) (+ ovals!!i * ovals!!j) ovals

-- | apply a Swap gate
applySwap :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applySwap i j (Pathsum s d o p pp ovals) = Pathsum s d o p pp ovals' where
  ovals' = set (ix i) (ovals!!j) $ set (ix j) (ovals!!i) ovals

-- | apply a multiply controlled Toffoli gate
applyMCT :: (Eq g, Abelian g, Dyadic g) => [Int] -> Int -> Pathsum g -> Pathsum g
applyMCT xs t (Pathsum s d o p pp ovals) = Pathsum s d o p pp ovals' where
  ovals' = over (ix t) (+ foldr (*) 1 (map (ovals!!) xs)) ovals

-- | apply a multiply controlled Z gate
applyMCZ :: (Eq g, Abelian g, Dyadic g) => [Int] -> Pathsum g -> Pathsum g
applyMCZ xs (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals where
  pp' = pp + distribute 1 (foldr (*) 1 (map (ovals!!) xs))

-- | apply a multiply controlled Rz gate
applyMCRz :: (Eq g, Abelian g, Dyadic g) => g -> [Int] -> Pathsum g -> Pathsum g
applyMCRz theta xs (Pathsum s d o p pp ovals) = Pathsum s d o p pp' ovals where
  pp' = pp + distribute (theta) (foldr (*) 1 (map (ovals!!) xs))

{----------------------------
 Channels
 ----------------------------}

-- | Choi matrix of computational basis measurement
measureChoi :: (Eq g, Abelian g) => Pathsum g
measureChoi = Pathsum 2 2 2 1 (lift $ y * (x0 + x1)) [x0, x1]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1
        y  = ofVar $ PVar 0

-- | CPM operator of computational basis measurement
measure :: (Eq g, Abelian g) => Pathsum g
measure = unChoi measureChoi

{----------------------------
 Bind, unbind, and subst
 ----------------------------}

-- | Bind some collection of free variables in a path sum
bind :: (Foldable f, Eq g, Abelian g) => f String -> Pathsum g -> Pathsum g
bind = flip (foldr go)
  where go x sop =
          let v = IVar $ inDeg sop in
            sop { inDeg = (inDeg sop) + 1,
                  phasePoly = subst (FVar x) (ofVar v) (phasePoly sop),
                  outVals = map (subst (FVar x) (ofVar v)) (outVals sop) }

-- | Close a path sum by binding all free variables
close :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
close sop = bind (freeVars sop) sop

-- | Unbind (instantiate) some collection of inputs
unbind :: (Foldable f, Eq g, Abelian g) => f Int -> Pathsum g -> Pathsum g
unbind xs (Pathsum a b c d e f) = Pathsum a (b - length xs) c d e' f' where
  e'  = substMany sub e
  f'  = map (substMany sub) f
  sub = \v -> Map.findWithDefault (ofVar v) v tmp
  tmp = snd $ foldr buildMap (0, Map.empty) [0..b-1]
  buildMap i (j, acc) = case i `elem` xs of
    True  -> (j, Map.insert (IVar i) (ofVar . FVar $ "#" ++ show (IVar i)) acc)
    False -> (j+1, Map.insert (IVar i) (ofVar . IVar $ j) acc)

-- | Open a path sum by instantiating all inputs
open :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
open sop = unbind [0..(inDeg sop) - 1] sop

-- | Substitute a monomial with a symbolic Boolean expression throughout
--
--   This is generally not a very safe thing to do. Convenience for certain
--   local transformations
substitute :: (Eq g, Abelian g) => [Var] -> SBool Var -> Pathsum g -> Pathsum g
substitute xs p (Pathsum a b c d e f) = Pathsum a b c d e' f' where
  e' = substMonomial xs p e
  f' = map (substMonomial xs p) f

{----------------------------
 Operators
 ----------------------------}

-- | Return the dual of a path sum
dualize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
dualize sop@(Pathsum a b c d e f) = inSOP .> midSOP .> outSOP
  where inSOP  = tensor (identity c) (etaN b)
        midSOP = tensor (tensor (identity c) sop) (identity b)
        outSOP = tensor (epsilonN c) (identity b)

-- | Return the (column) vectorized path sum. By convention we place the inputs
--   first (i.e. f : A -> B becomes vectorize f : A* \otimes B)
vectorize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
vectorize sop@(Pathsum a b c d e f) = etaN b .> tensor (identity b) sop

-- | Return the (row) vectorized path sum. By convention we place the outputs
--   first (i.e. f : A -> B becomes vectorize f : A* \otimes B)
covectorize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
covectorize sop@(Pathsum a b c d e f) = tensor (identity c) sop .> epsilonN c

-- | Take the dagger of a path sum
dagger :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
dagger (Pathsum a b c d e f) = dualize $ Pathsum a b c d (-e) f

-- | Take the conjugate (c.f., lower star) of a path sum
conjugate :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
conjugate (Pathsum a b c d e f) = Pathsum a b c d (-e) f

-- | Trace a square morphism. Throws an error if the input and outputs are not
--   the same size
trace :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
trace sop@(Pathsum a b c d e f)
  | b /= c = error "Can't trace a non-square operator"
  | otherwise = etaN b .> tensor (identity b) sop .> epsilonN b

-- | Trace out the first qubit. Throws an error if the input is a vector
ptrace :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
ptrace sop@(Pathsum a b c d e f)
  | b < 1 || c < 1 = error "Can't partial trace a vector"
  | otherwise = tensor eta (identity $ b-1) .>
                tensor (identity 1) sop .>
                tensor epsilon (identity $ c-1)

-- | Turn a pure state into a density matrix. Throws an error if the input is not
--   a column vector
densify :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
densify sop@(Pathsum a b c d e f)
  | b /= 0 = error "Can't densify an operator "
  | otherwise = dagger sop .> sop

-- | Turn a (single-qubit) Choi matrix into a CPM-style linear operator
unChoi :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
unChoi sop@(Pathsum a b c d e f)
  | b /= 2 || c /= 2 = error "Only single-qubit channels currently supported"
  | otherwise        = tensor eta swapgate .>
                       tensor (identity 1) (tensor sop $ identity 1) .>
                       tensor swapgate epsilon

-- | Turn a unitary operator into a channel. That is, f becomes f_* \otimes f
channelize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
channelize sop = tensor (conjugate sop) sop

-- | Construct a controlled path sum
controlled :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
controlled sop@(Pathsum a b c d e f) = Pathsum a (b+1) (c+1) d e' f' where
  shift   = shiftI 1
  x       = ofVar $ IVar 0
  e'      = (lift x)*(renameMonotonic shift e)
  f'      = [lift x] ++ (map g . zip [1..] . map (renameMonotonic shift) $ f)
  g (i,y) = (ofVar $ IVar i) + x*((ofVar $ IVar i) + y)

-- | Attempt to add two path sums. Only succeeds if the resulting sum is balanced
--   and the dimensions match.
plusMaybe :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Maybe (Pathsum g)
plusMaybe sop sop'
  | inDeg sop  /= inDeg sop'                                       = Nothing
  | outDeg sop /= outDeg sop'                                      = Nothing
  | (sde sop) + 2*(pathVars sop') /= (sde sop') + 2*(pathVars sop) = Nothing
  | otherwise = Just $ Pathsum sde' inDeg' outDeg' pathVars' phasePoly' outVals'
  where sde'       = (sde sop) + 2*(pathVars sop')
        inDeg'     = inDeg sop
        outDeg'    = outDeg sop
        pathVars'  = (pathVars sop) + (pathVars sop') + 1
        y          = ofVar $ PVar (pathVars' - 1)
        phasePoly' = (lift y)*(phasePoly sop) +
                     (lift (1+y))*(renameMonotonic shift $ phasePoly sop')
        outVals'   = map (\(a,b) -> b + y*(a + b)) $
                       zip (outVals sop) (map (renameMonotonic shift) $ outVals sop')
        shift x    = case x of
          PVar i -> PVar $ i + (pathVars sop)
          _      -> x

-- | Construct the sum of two path sums. Raises an error if the sums are incompatible
plus :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
plus sop sop' = case plusMaybe sop sop' of
  Nothing    -> error "Incompatible path sums"
  Just sop'' -> sop''

-- | Compose two path sums in parallel
tensor :: (Eq g, Num g) => Pathsum g -> Pathsum g -> Pathsum g
tensor sop sop' = Pathsum sde' inDeg' outDeg' pathVars' phasePoly' outVals'
  where sde'       = (sde sop) + (sde sop')
        inDeg'     = (inDeg sop) + (inDeg sop')
        outDeg'    = (outDeg sop) + (outDeg sop')
        pathVars'  = (pathVars sop) + (pathVars sop')
        phasePoly' = (phasePoly sop) + (renameMonotonic shift $ phasePoly sop')
        outVals'   = (outVals sop) ++ (map (renameMonotonic shift) $ outVals sop')
        shift x    = case x of
          IVar i -> IVar $ i + (inDeg sop)
          PVar i -> PVar $ i + (pathVars sop)
          _      -> x

-- | Attempt to compose two path sums in sequence. Only succeeds if the dimensions
--   are compatible (i.e. if the out degree of the former is the in degree of the
--   latter)
timesMaybe :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Maybe (Pathsum g)
timesMaybe sop sop'
  | outDeg sop /= inDeg sop' = Nothing
  | otherwise = Just $ Pathsum sde' inDeg' outDeg' pathVars' phasePoly' outVals'
  where sde'       = (sde sop) + (sde sop')
        inDeg'     = inDeg sop
        outDeg'    = outDeg sop'
        pathVars'  = (pathVars sop) + (pathVars sop')
        phasePoly' = (phasePoly sop) +
                     (substMany sub . renameMonotonic shift $ phasePoly sop')
        outVals'   = (map (substMany sub . renameMonotonic shift) $ outVals sop')
        shift x    = case x of
          PVar i -> PVar $ i + (pathVars sop)
          _      -> x
        sub x      = case x of
          IVar i -> (outVals sop)!!i
          _      -> ofVar x

-- | Compose two path sums in sequence. Throws an error if the dimensions are
--   not compatible
times :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
times sop sop' = case timesMaybe sop sop' of
  Nothing    -> error "Incompatible path sum dimensions"
  Just sop'' -> sop''

-- | Left-to-right composition
(.>) :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
(.>) = times

infixr 5 .>

-- | Scale the normalization factor
renormalize :: Int -> Pathsum g -> Pathsum g
renormalize k (Pathsum a b c d e f) = Pathsum (a + k) b c d e f

-- | Embed a path sum into a larger space with a specified input and
--   output embedding.
embed :: (Eq g, Abelian g) => Pathsum g -> Int -> (Int -> Int) -> (Int -> Int) -> Pathsum g
embed sop n embedIn embedOut
  | n < 0     = error "Can't embed in smaller space"
  | otherwise = inPerm .> tensor (identity n) sop .> outPerm where
      mIn = inDeg sop
      ins = map embedIn [0..mIn-1]
      inPerm  = permutation $ ([0..mIn+n-1] \\ ins) ++ ins
      mOut = outDeg sop
      outs = map embedOut [0..mOut-1]
      outPerm = unpermutation $ ([0..mOut+n-1] \\ outs) ++ outs

-- | Drop a qubit
discard :: Eq g => Int -> Pathsum g -> Pathsum g
discard i sop@(Pathsum a b c d e f) = Pathsum a b' c' d e f' where
  b' = if i < b then b-1 else b
  c' = if i < c then c-1 else c
  f' = snd . unzip . filter (\(j,_) -> i /= j) $ zip [0..] f

{--------------------------
 Type class instances
 --------------------------}
  
instance (Eq g, Num g) => Semigroup (Pathsum g) where
  (<>) = tensor

instance (Eq g, Num g) => Monoid (Pathsum g) where
  mempty  = Pathsum 0 0 0 0 0 []
  mappend = (<>)

instance (Eq g, Abelian g) => Num (Pathsum g) where
  (+)                          = plus
  (*)                          = (flip times)
  negate (Pathsum a b c d e f) = Pathsum a b c d (lift 1 + e) f
  abs (Pathsum a b c d e f)    = Pathsum a b c d (dropConstant e) f
  signum sop                   = sop
  fromInteger                  = identity . fromInteger

instance Functor Pathsum where
  fmap g (Pathsum a b c d e f) = Pathsum a b c d (cast g e) f

{--------------------------
 Reduction rules
 --------------------------}

{-
class RewriteRule rule g where
  matchAll :: Pathsum g -> [rule]
  matchOne :: Pathsum g -> rule
  apply :: rule -> Pathsum g -> Pathsum g

data E = E !Var {-# UNBOX #-}

instance (Eq g, Periodic g) => RewriteRule E g where
  match = matchElim
  apply = applyElim
-}

-- | Maps the order 1 and order 2 elements of a group to FF2
injectFF2 :: Periodic g => g -> Maybe FF2
injectFF2 a = case order a of
  1 -> Just 0
  2 -> Just 1
  _ -> Nothing

-- | Gives a Boolean polynomial equivalent to the current polynomial, if possible
toBooleanPoly :: (Eq g, Periodic g) => PseudoBoolean v g -> Maybe (SBool v)
toBooleanPoly = castMaybe injectFF2

-- | Elim rule. \(\dots(\sum_y)\dots = \dots 2 \dots\)
matchElim :: (Eq g, Periodic g) => Pathsum g -> [Var]
matchElim sop = msum . (map go) $ internalPaths sop
  where go v = if Set.member v (vars $ phasePoly sop) then [] else [v]

-- | Generic HH rule. \(\dots(\sum_y (-1)^{y\cdot f})\dots = \dots|_{f = 0}\)
matchHH :: (Eq g, Periodic g) => Pathsum g -> [(Var, SBool Var)]
matchHH sop = msum . (map (maybeToList . go)) $ internalPaths sop
  where go v = toBooleanPoly (quotVar v $ phasePoly sop) >>= \p -> return (v, p)

-- | Solvable instances of the HH rule.
--   \(\dots(\sum_y (-1)^{y(z \oplus f)})\dots = \dots[z \gets f]\)
matchHHSolve :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHSolve sop = do
  (v, p)   <- matchHH sop
  (v', p') <- solveForX p
  case v' of
    PVar _ -> return (v, v', p')
    _      -> mzero

-- | Instances of the HH rule with a linear substitution
matchHHLinear :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHLinear sop = do
  (v, p)   <- filter ((<= 1) . degree . snd) $ matchHH sop
  (v', p') <- solveForX p
  case v' of
    PVar _ -> return (v, v', p')
    _      -> mzero

-- | Instances of the HH rule with only internal substitutions
matchHHInternal :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHInternal sop = do
  (v, p)   <- matchHH sop
  (v', p') <- filter ((flip elem) (internalPaths sop) . fst) $ solveForX p
  case v' of
    PVar _ -> return (v, v', p')
    _      -> mzero

-- | Instances of the \(\omega\) rule
matchOmega :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> [(Var, SBool Var)]
matchOmega sop = do
  v <- internalPaths sop
  p <- maybeToList . toBooleanPoly . addFactor v $ phasePoly sop
  return (v, p)
  where addFactor v p = constant (fromDyadic $ dyadic 3 1) + quotVar v p

-- | Instances of the var rule
matchVar :: Eq g => Pathsum g -> [(Var, SBool Var)]
matchVar sop = do
  p       <- outVals sop
  (v, p') <- solveForX p
  case (v, p') of
    (_, 0)      -> mzero
    (PVar _, p) -> return (v, ofVar v + p')
    _           -> mzero
  
{--------------------------
 Pattern synonyms
 --------------------------}

-- | Ordering of solvable hh instances
hhOrder :: (Var, Var, SBool Var) -> (Var, Var, SBool Var) -> Ordering
hhOrder (_,_,p) (_,_,q) = compare (length $ toTermList p) (length $ toTermList q)

-- | Pattern synonym for Elim
pattern Triv :: (Eq g, Num g) => Pathsum g
pattern Triv <- (isTrivial -> True)

-- | Pattern synonym for Elim
pattern Elim :: (Eq g, Periodic g) => Var -> Pathsum g
pattern Elim v <- (matchElim -> (v:_))

-- | Pattern synonym for HH
pattern HH :: (Eq g, Periodic g) => Var -> SBool Var -> Pathsum g
pattern HH v p <- (matchHH -> (v, p):_)

-- | Pattern synonym for solvable HH instances
pattern HHSolved :: (Eq g, Periodic g) => Var -> Var -> SBool Var -> Pathsum g
pattern HHSolved v v' p <- (matchHHSolve -> (v, v', p):_)

-- | Pattern synonym for linear HH instances
pattern HHLinear :: (Eq g, Periodic g) => Var -> Var -> SBool Var -> Pathsum g
pattern HHLinear v v' p <- (matchHHLinear -> (v, v', p):_)

-- | Pattern synonym for internal HH instances
pattern HHInternal :: (Eq g, Periodic g) => Var -> Var -> SBool Var -> Pathsum g
pattern HHInternal v v' p <- (matchHHInternal -> (v, v', p):_)

-- | Pattern synonym for HH instances where the polynomial is strictly a
--   function of input variables
pattern HHKill :: (Eq g, Periodic g) => Var -> SBool Var -> Pathsum g
pattern HHKill v p <- (filter (all (not . isP) . vars . snd) . matchHH -> (v, p):_)

-- | Pattern synonym for Omega instances
pattern Omega :: (Eq g, Periodic g, Dyadic g) => Var -> SBool Var -> Pathsum g
pattern Omega v p <- (matchOmega -> (v, p):_)

-- | Pattern synonym for var instances
pattern Var :: Eq g => Var -> SBool Var -> Pathsum g
pattern Var v p <- (matchVar -> (v, p):_)

{--------------------------
 Applying reductions
 --------------------------}

-- | Apply an elim rule. Does not check if the instance is valid
applyElim :: Var -> Pathsum g -> Pathsum g
applyElim (PVar i) (Pathsum a b c d e f) = Pathsum (a-2) b c (d-1) e' f'
  where e' = renameMonotonic varShift e
        f' = map (renameMonotonic varShift) f
        varShift (PVar j)
          | j > i     = PVar $ j - 1
          | otherwise = PVar $ j
        varShift v = v

-- | Apply a (solvable) HH rule. Does not check if the instance is valid
applyHHSolved :: (Eq g, Abelian g) => Var -> Var -> SBool Var -> Pathsum g -> Pathsum g
applyHHSolved (PVar i) v p (Pathsum a b c d e f) = Pathsum a b c (d-1) e' f'
  where e' = renameMonotonic varShift . subst v p . remVar (PVar i) $ e
        f' = map (renameMonotonic varShift . subst v p) f
        varShift (PVar j)
          | j > i     = PVar $ j - 1
          | otherwise = PVar $ j
        varShift v = v

-- | Apply an (\omega\) rule. Does not check if the instance is valid
applyOmega :: (Eq g, Abelian g, Dyadic g) => Var -> SBool Var -> Pathsum g -> Pathsum g
applyOmega (PVar i) p (Pathsum a b c d e f) = Pathsum (a-1) b c (d-1) e' f'
  where e' = renameMonotonic varShift $ p' + remVar (PVar i) e
        f' = map (renameMonotonic varShift) f
        p' = constant (fromDyadic $ dyadic 1 2) + distribute (fromDyadic $ dyadic 3 1) (lift p)
        varShift (PVar j)
          | j > i     = PVar $ j - 1
          | otherwise = PVar $ j
        varShift v = v

-- | Apply a var rule. Does not check if the instance is valid
applyVar :: (Eq g, Abelian g) => Var -> SBool Var -> Pathsum g -> Pathsum g
applyVar v p (Pathsum a b c d e f) = Pathsum a b c d (subst v p e) (map (subst v p) f)

-- | Finds and applies the first elimination instance
rewriteElim :: (Eq g, Periodic g) => Pathsum g -> Pathsum g
rewriteElim sop = case sop of
  Elim v -> applyElim v sop
  _      -> sop

-- | Finds and applies the first hh instance
rewriteHH :: (Eq g, Periodic g) => Pathsum g -> Pathsum g
rewriteHH sop = case sop of
  HHSolved v v' p -> applyHHSolved v v' p sop
  _               -> sop

-- | Finds and applies the first omega instance
rewriteOmega :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Pathsum g
rewriteOmega sop = case sop of
  Omega v p -> applyOmega v p sop
  _         -> sop

-- | Finds and applies the first var instance
rewriteVar :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
rewriteVar sop = case sop of
  Var v p -> applyVar v p sop
  _       -> sop

-- | Abstracts a monomial into a fresh path variable. The reverse of an HH
abstractMono :: (Eq g, Abelian g) => [Var] -> Pathsum g -> Pathsum g
abstractMono m (Pathsum a b c d e f) = Pathsum a' b c (d + 2) e' f' where
  y = ofVar $ PVar d
  z = ofVar $ PVar (d+1)
  a' = a + 2
  e' = substMonomial m z e + (distribute 1 $ y*(ofMonomial (monomial m) + z))
  f' = map (substMonomial m z) f

{--------------------------
 Reduction procedures
 --------------------------}

-- | Performs basic simplifications
simplify :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Pathsum g
simplify sop = case sop of
  Elim y         -> simplify $ applyElim y sop
  HHLinear y z p -> simplify $ applyHHSolved y z p sop
  Omega y p      -> simplify $ applyOmega y p sop
  _              -> sop

-- | The rewrite system of M. Amy,
--   / Towards Large-Scaled Functional Verification of Universal Quantum Circuits /, QPL 2018.
--   Generally effective at evaluating (symbolic) values.
grind :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Pathsum g
grind sop = case sop of
  Elim y         -> grind $ applyElim y sop
  Omega y p      -> grind $ applyOmega y p sop
  HHSolved y z p -> grind $ applyHHSolved y z p sop
  _              -> sop

-- | A normalization procedure for Clifford circuits
normalizeClifford :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Pathsum g
normalizeClifford sop = go $ sop .> hLayer .> hLayer where
  hLayer = foldr (<>) mempty $ replicate (outDeg sop) hgate
  go sop = case sop of
    Elim y           -> go $ applyElim y sop
    HHInternal y z p -> go $ applyHHSolved y z p sop
    Omega y p        -> go $ applyOmega y p sop
    HHSolved y z p   -> go $ applyHHSolved y z p sop
    _                -> sop

{--------------------------
 Simulation
 --------------------------}

-- | Gets the cofactors of some path variable
expand :: (Eq g, Abelian g) => Pathsum g -> Var -> (Pathsum g, Pathsum g)
expand (Pathsum a b c d e f) v = (p0, p1) where
  p0  = Pathsum a b c (d-1) (subst v 0 e) (map (subst v 0) f)
  p1  = Pathsum a b c (d-1) (subst v 1 e) (map (subst v 1) f)

-- | Simulates a pathsum on a given input
simulate :: (Eq g, Periodic g, Dyadic g, Real g, RealFloat f) => Pathsum g -> [FF2] -> Map [FF2] (Complex f)
simulate sop xs = go $ sop * ket (map constant xs)
  where go      = go' . grind
        go' ps  = case ps of
          (Pathsum k 0 _ 0 p xs) ->
            let phase     = fromRational . toRational $ getConstant p
                base      = case k `mod` 2 of
                  0 -> fromInteger $ 1 `shiftL` (abs k)
                  1 -> sqrt(2.0) * (fromInteger $ 1 `shiftL` (abs (k-1)))
                magnitude = base**(fromIntegral $ signum k)
            in
              Map.singleton (map getConstant xs) (mkPolar magnitude (pi * phase))
          (Pathsum k 0 n i p xs) ->
            let v     = PVar $ i-1
                left  = go (Pathsum k 0 n (i-1) (subst v zero p) (map (subst v zero) xs))
                right = go (Pathsum k 0 n (i-1) (subst v one p) (map (subst v one) xs))
            in
              Map.unionWith (+) left right
          _                      -> error "Incompatible dimensions"

-- | Evaluates a pathsum on a given input and output
amplitude :: (Eq g, Periodic g, Dyadic g, Real g, RealFloat f) => [FF2] -> Pathsum g -> [FF2] -> Complex f
amplitude o sop i = (simulate (bra (map constant o) * sop) i)![]

-- | Checks identity by checking inputs iteratively
isIdentity :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Bool
isIdentity sop
  | isTrivial sop = True
  | otherwise     = case inDeg sop of
      0 -> False
      i -> let p0 = (grind $ identity (i-1) <> ket [0] .> sop .> identity (i-1) <> bra [0])
               p1 = (grind $ identity (i-1) <> ket [1] .> sop .> identity (i-1) <> bra [1])
           in
             isIdentity p0 && isIdentity p1

-- | Checks whether a state is the density matrix of a pure state by computing the purity
isPure :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Bool
isPure sop
  | inDeg sop /= outDeg sop = False
  | otherwise               = purity == identity 0 where
      purity = trace $ sop .> sop

{--------------------------
 Testing
 --------------------------}

-- | Test suite for internal use
runTests :: () -> IO ()
runTests _ = do
  print $ isIdentity (applyX 0 (xgate :: Pathsum DMod2))
  print $ isIdentity (applyY 0 (ygate :: Pathsum DMod2))
  print $ isIdentity (applyZ 0 (zgate :: Pathsum DMod2))
  print $ isIdentity (applyS 0 (sdggate :: Pathsum DMod2))
  print $ isIdentity (applySdg 0 (sgate :: Pathsum DMod2))
  print $ isIdentity (applyT 0 (tdggate :: Pathsum DMod2))
  print $ isIdentity (applyTdg 0 (tgate :: Pathsum DMod2))
  print $ isIdentity (applyH 0 (hgate :: Pathsum DMod2))
  print $ isIdentity (applyCZ 0 1 (czgate :: Pathsum DMod2))
  print $ isIdentity (applyCX 0 1 (cxgate :: Pathsum DMod2))
  print $ isIdentity (applySwap 0 1 (swapgate :: Pathsum DMod2))
  print $ isIdentity (applyCCZ 0 1 2 (cczgate :: Pathsum DMod2))
  print $ isIdentity (applyCCX 0 1 2 (ccxgate :: Pathsum DMod2))
  print $ isIdentity (applyMCT [0,1,2] 3 (mctgate 3 :: Pathsum DMod2))
  print $ isIdentity (applyCX 1 0 (swapgate .> cxgate .> swapgate :: Pathsum DMod2))
  print $ applyX 0 (identity 1) == (xgate :: Pathsum DMod2)
  print $ applyY 0 (identity 1) == (ygate :: Pathsum DMod2)
  print $ applyZ 0 (identity 1) == (zgate :: Pathsum DMod2)
  print $ applyS 0 (identity 1) == (sgate :: Pathsum DMod2)
  print $ applySdg 0 (identity 1) == (sdggate :: Pathsum DMod2)
  print $ applyT 0 (identity 1) == (tgate :: Pathsum DMod2)
  print $ applyTdg 0 (identity 1) == (tdggate :: Pathsum DMod2)
  print $ applyH 0 (identity 1) == (hgate :: Pathsum DMod2)
  print $ applyCZ 0 1 (identity 2) == (czgate :: Pathsum DMod2)
  print $ applyCX 0 1 (identity 2) == (cxgate :: Pathsum DMod2)
  print $ applySwap 0 1 (identity 2) == (swapgate :: Pathsum DMod2)
  print $ applyCCZ 0 1 2 (identity 3) == (cczgate :: Pathsum DMod2)
  print $ applyCCX 0 1 2 (identity 3) == (ccxgate :: Pathsum DMod2)
  print $ applyMCT [0,1,2] 3 (identity 4) == (mctgate 3 :: Pathsum DMod2)
  print $ applyCX 1 0 (identity 2) == (swapgate .> cxgate .> swapgate :: Pathsum DMod2)

{--------------------------
 Examples
 --------------------------}

-- | A symbolic state |x>
sstate :: Pathsum DMod2
sstate = open $ identity 1

-- | A bell state
bellstate :: Pathsum DMod2
bellstate = fresh <> fresh .> hgate <> (identity 1) .> cxgate

-- | Teleportation circuit
teleport :: Pathsum DMod2
teleport = (identity 1) <> bellstate .>
           cxgate <> (identity 1) .>
           hgate <> cxgate .>
           swapgate <> hgate .>
           (identity 1) <> cxgate .>
           swapgate <> hgate

-- | Teleportation channel
teleportChannel :: Pathsum DMod2
teleportChannel = channelize ((identity 1) <> bellstate) .>
                  channelize (cxgate <> (identity 1)) .>
                  channelize (hgate <> cxgate) .>
                  embed measure 4 (* 3) (* 3) .>
                  embed measure 4 (\i -> i*3 + 1) (\j -> j*3 + 1) .>
                  channelize (swapgate <> hgate) .>
                  channelize ((identity 1) <> cxgate) .>
                  channelize (swapgate <> hgate) .>
                  embed epsilon 4 (* 3) (* 3) .> -- trace out first qubit
                  embed epsilon 2 (* 2) (* 2)    -- trace out second
           
-- | Verify teleportation
verifyTele :: () -> IO ()
verifyTele _ = case (densify sstate == grind (ptrace . ptrace . densify $ sstate .> teleport)) of
  True -> putStrLn "Identity"
  False -> putStrLn "Not identity"
  
-- | Verify teleportation channel
verifyTeleC :: () -> IO ()
verifyTeleC _ = case (rho == grind (rho .> teleportChannel)) of
  True -> putStrLn "Identity"
  False -> putStrLn "Not identity"
  where rho = grind $ vectorize $ densify sstate

-- | The |A> = T|+> state
aState :: Pathsum DMod2
aState = fresh .> hgate .> tgate

-- | T gate teleportation channel
teleportTChannel :: Pathsum DMod2
teleportTChannel = channelize ((identity 1) <> aState) .>
                   channelize (cxgate) .>
                   embed measure 2 (\i -> i*2 + 1) (\j -> j*2 + 1) .>
                   channelize (controlled sgate) .>
                   embed epsilon 2 (\i -> i*2 + 1) (\j -> j*2 + 1) -- trace out the resource state

-- | Verify teleportation channel
verifyTeleT :: () -> IO ()
verifyTeleT _ = case (channelize tgate == grind (teleportTChannel)) of
  True -> putStrLn "Identity"
  False -> putStrLn "No identity"

-- | Relation 13 from Bian and Selinger's presentation of the 2-qubit Clifford+T group
cliffordT13 :: Pathsum DMod2
cliffordT13 = c .> c where
  c = cxgate .>
      xgate <> (tgate .> hgate .> tgate .> hgate .> tdggate) .>
      cxgate .>
      xgate <> (tgate .> hgate .> tdggate .> hgate .> tdggate)

-- | Pipeline for applying rewrites in sequence
(|>) :: a -> (a -> b) -> b
a |> f = f a

infixl 1 |>

-- | A manual proof of 13
cliffordT13_is_identity () = case isIdentity reducedSOP of
  True -> putStrLn "Identity"
  False -> putStrLn "Not identity"
  where reducedSOP =
          let c1      = vectorize cliffordT13
              c2      = abstractMono [PVar 0, PVar 5] c1
              (a,b,c) = head $ tail $ matchHHSolve c2
              c3      = applyHHSolved a b c c2
              c4      = rewriteElim c3
              c5      = rewriteOmega c4
              c6      = applyVar (PVar 0) (ofVar (PVar 0) + 1) c5
              c7      = abstractMono [PVar 0, PVar 5] c6
              (e,f,g) = head $ matchHHSolve c7
              c8      = applyHHSolved e f g c7
              c9      = rewriteElim c8
              c10     = rewriteHH c9
              c11     = rewriteElim c10
              c12     = grind c11
          in
            grind $ (identity 2 <> c12) .> (epsilonN 2 <> identity 2)
              
-- | Relation 14 from Bian and Selinger's presentation of the 2-qubit Clifford+T group
cliffordT14 :: Pathsum DMod2
cliffordT14 =
  x1 .>
  cxgate .>
  x1 .>
  t2 .>
  h2 .>
  t2 .>
  h2 .>
  tdg2 .>
  cxgate .>
  sdg1 .>
  t2 .>
  h1 .>
  h2 .>
  tdg1 .>
  s2 .>
  tdg2 .>
  x2 .>
  xcgate .>
  x2 .>
  t1 .>
  h1 .>
  t1 .>
  h1 .>
  tdg1 .>
  xcgate .>
  t1 .>
  t2 .>
  h1 .>
  sdg2 .>
  s1 .>
  h2 .>
  tdg1 .>
  tdg2 .>
  cxgate .>
  t2 .>
  h2 .>
  tdg2 .>
  h2 .>
  tdg2 .>
  x1 .>
  cxgate .>
  x1 .>
  t2 .>
  t1 .>
  h2 .>
  sdg1 .>
  s2 .>
  h1 .>
  tdg1 .>
  xcgate .>
  t1 .>
  h1 .>
  tdg1 .>
  h1 .>
  tdg1 .>
  x2 .>
  xcgate .>
  x2 .>
  t1 .>
  h1 .>
  sdg2 .>
  s1 .>
  h2 .>
  tdg2
  where x1 = xgate <> identity 1
        x2 = identity 1 <> xgate
        h1 = hgate <> identity 1
        h2 = identity 1 <> hgate
        t1 = tgate <> identity 1
        t2 = identity 1 <> tgate
        s1 = sgate <> identity 1
        s2 = identity 1 <> sgate
        tdg1 = tdggate <> identity 1
        tdg2 = identity 1 <> tdggate
        sdg1 = sdggate <> identity 1
        sdg2 = identity 1 <> sdggate
        xcgate = swapgate .> cxgate .> swapgate
