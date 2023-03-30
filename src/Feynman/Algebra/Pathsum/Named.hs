{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}

{-|
Module      : Named
Description : Amplitude-balanced path sums w/ named representation
Copyright   : (c) Matthew Amy, 2023
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Pathsum.Named where

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

-- | Variables can be denoted as input (lambda-bound), path (sigma-bound), or free
data VarType = IVar | PVar | FVar deriving (Eq)

instance Ord VarType where
  compare a b | a == b = EQ
  compare PVar _    = GT
  compare _ PVar    = LT
  compare IVar FVar = GT
  compare FVar IVar = LT

data Var = Var { vname :: String, vtype :: VarType } deriving (Eq)

instance Ord Var where
  compare a b | cmp == EQ = compare (vname a) (vname b)
              | otherwise = cmp
                where cmp = compare (vtype a) (vtype b)

instance Show Var where
  show = vname

instance IsString Var where
  fromString s = Var s FVar

-- | Convenience function for the string representation of xi
xi :: Int -> String
xi = U.sub "x" . fromIntegral

-- | Convenience function for the string representation of yi
yi :: Int -> String
yi = U.sub "y" . fromIntegral

-- | Convenience function for the string representation of zi
zi :: Int -> String
zi = U.sub "z" . fromIntegral

-- | Convenience function for a standard input variable
ivar :: Int -> Var
ivar i = Var (xi i) IVar

-- | Convenience function for a standard path variable
pvar :: Int -> Var
pvar i = Var (yi i) PVar

-- | Convenience function for a free variable
fvar :: String -> Var
fvar s = Var s FVar

-- | Check if a variable is an input
isI :: Var -> Bool
isI (Var _ IVar) = True
isI _            = False

-- | Check if a variable is a path variable
isP :: Var -> Bool
isP (Var _ PVar) = True
isP _            = False

-- | Check if a variable is a free variable
isF :: Var -> Bool
isF (Var _ FVar) = True
isF _            = False

{-----------------------------------
 Path sums
 -----------------------------------}

-- | Path sums of the form
--   \(\frac{1}{\sqrt{2}^k}\sum_{y\in\mathbb{Z}_2^m}e^{i\pi P(x, y)}|f(x, y)\rangle\)
data Pathsum g = Pathsum {
  sde       :: !Int,
  inVals    :: ![Var],
  pathVars  :: ![Var],
  phasePoly :: !(PseudoBoolean Var g),
  outVals   :: ![SBool Var]
  } deriving (Eq)

instance (Show g, Eq g, Periodic g, Real g) => Show (Pathsum g) where
  show sop = inputstr ++ scalarstr ++ sumstr ++ amplitudestr ++ statestr
    where inputstr = case inVals sop of
            [] -> ""
            xs -> U.ket (concatMap show xs) ++ " " ++ U.mapsto ++ " "
          scalarstr = case compare (sde sop) 0 of
            LT -> U.sup ("(" ++ U.rt2 ++ ")") (fromIntegral . abs $ sde sop)
            EQ -> if (inDeg sop == 0 && outDeg sop == 0 && phasePoly sop == 0) then "1" else ""
            GT -> U.sup ("1/(" ++ U.rt2 ++ ")") (fromIntegral $ sde sop)
          sumstr = case pathVars sop of
            [] -> ""
            xs -> U.sum ++ "[" ++ concatMap show xs ++ "]"
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
internalPaths sop = pathVars sop \\ outVars
  where outVars = Set.toList . Set.unions . map vars $ outVals sop

-- | Retrieve the free variables
freeVars :: Pathsum g -> [Var]
freeVars sop = Set.toList . Set.filter isF . foldr (Set.union) Set.empty $ xs
  where xs = (vars $ phasePoly sop):(map vars $ outVals sop)

-- | Checks if the path sum is (trivially) the identity
isTrivial :: (Eq g, Num g) => Pathsum g -> Bool
isTrivial sop = sop == identity (inDeg sop)

-- | Convenience function for the input degree
inDeg :: Pathsum g -> Int
inDeg = length . inVals

-- | Convenience function for the output degree
outDeg :: Pathsum g -> Int
outDeg = length . outVals

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
identity n = Pathsum 0 ivars [] 0 (map ofVar ivars)
  where ivars = [ivar i | i <- [0..n-1]]

-- | Construct a (symbolic) state
ofKet :: (Eq g, Num g) => [SBool String] -> Pathsum g
ofKet xs = Pathsum 0 [] [] 0 $ map (rename (\x -> Var x FVar)) xs

-- | Initialize a fresh ancilla
initialize :: (Eq g, Num g) => FF2 -> Pathsum g
initialize b = ofKet [constant b]

{-# INLINE initialize #-}

-- | Construct an n-ary unit
etaN :: (Eq g, Num g) => Int -> Pathsum g
etaN n = Pathsum 0 [] pvars 0 $ xs ++ xs
  where pvars = [pvar i | i <- [0..n-1]]
        xs    = map ofVar pvars

{----------------------------
 Dual constructors
 ----------------------------}

-- | Construct a (symbolic) state destructor
ofBra :: (Eq g, Abelian g) => [SBool String] -> Pathsum g
ofBra xs = Pathsum (2*(length xs)) ivars pvars (lift poly) []
  where ivars = [ivar i | i <- [0..length xs - 1]]
        pvars = [pvar i | i <- [0..length xs - 1]]
        poly      = foldr (+) 0 . map go $ zip [0..] xs
        go (i, q) = ofVar (pvar i) * (ofVar (ivar i) + (rename (\x -> Var x FVar) q))

-- | Dagger of initialize -- i.e. unnormalized post-selection
postselect :: (Eq g, Abelian g) => FF2 -> Pathsum g
postselect b = ofBra [constant b]

{-# INLINE postselect #-}

-- | Construct an n-ary co-unit
epsilonN :: (Eq g, Abelian g) => Int -> Pathsum g
epsilonN n = Pathsum (2*n) ivars pvars (lift poly) []
  where ivars = [ivar i | i <- [0.. 2*n - 1]]
        pvars = [pvar i | i <- [0..n -1]]
        poly  = sum $ map f [0..n-1]
        f i   = ofVar (pvar i) * (ofVar (ivar i) + ofVar (ivar $ n+i))

{----------------------------
 Constants
 ----------------------------}

-- | \(\sqrt{2}\)
root2 :: (Eq g, Abelian g, Dyadic g) => Pathsum g
root2 = Pathsum 0 [] [pvar 0] ((-constant (half * half)) + scale half (lift $ ofVar (pvar 0))) []

-- | \(1/\sqrt{2}\)
roothalf :: (Eq g, Abelian g, Dyadic g) => Pathsum g
roothalf = Pathsum 1 [] [] 0 []

-- | \(i\)
iunit :: (Eq g, Abelian g, Dyadic g) => Pathsum g
iunit = Pathsum 0 [] [] (constant half) []

-- | \(e^{i\pi/4}\)
omega :: (Eq g, Abelian g, Dyadic g) => Pathsum g
omega = Pathsum 0 [] [] (constant (half * half)) []

-- | A fresh, 0-valued ancilla
fresh :: (Eq g, Num g) => Pathsum g
fresh = Pathsum 0 [] [] 0 [0]

-- | The dagger of fresh
unfresh :: (Eq g, Abelian g) => Pathsum g
unfresh = Pathsum 2 [ivar 0] [pvar 0] p []
  where p = lift $ ofVar (pvar 0) * ofVar (ivar 0)

-- | The unit, \(\eta\)
eta :: (Eq g, Num g) => Pathsum g
eta = Pathsum 0 [] [pvar 0] 0 [ofVar (pvar 0), ofVar (pvar 0)]

-- | The co-unit, \(\epsilon\)
epsilon :: (Eq g, Abelian g) => Pathsum g
epsilon = Pathsum 2 [ivar 0, ivar 1] [pvar 1] p []
  where p = lift $ ofVar (pvar 0) * (ofVar (ivar 0) + ofVar (ivar 1))

{----------------------------
 Matrices
 ----------------------------}

-- | X gate
xgate :: (Eq g, Num g) => Pathsum g
xgate = Pathsum 0 [ivar 0] [] 0 [1 + ofVar (ivar 0)]

-- | Z gate
zgate :: (Eq g, Abelian g) => Pathsum g
zgate = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = lift $ ofVar (ivar 0)

-- | Y gate
ygate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
ygate = Pathsum 0 [ivar 0] [] p [1 + ofVar (ivar 0)]
  where p = constant half + (lift $ ofVar (ivar 0))

-- | S gate
sgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
sgate = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale half (lift $ ofVar (ivar 0))

-- | S* gate
sdggate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
sdggate = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale (-half) (lift $ ofVar (ivar 0))

-- | T gate
tgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
tgate = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale (half*half) (lift $ ofVar (ivar 0))

-- | T* gate
tdggate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
tdggate = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale (-half*half) (lift $ ofVar (ivar 0))

-- | R_k gate
rkgate :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g
rkgate k = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale (fromDyadic $ dyadic 1 k) (lift $ ofVar (ivar 0))

-- | R_z gate
rzgate :: (Eq g, Abelian g, Dyadic g) => g -> Pathsum g
rzgate theta = Pathsum 0 [ivar 0] [] p [ofVar (ivar 0)]
  where p = scale theta (lift $ ofVar (ivar 0))

-- | H gate
hgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
hgate = Pathsum 1 [ivar 0] [pvar 0] p [ofVar (pvar 0)]
  where p = lift $ (ofVar $ ivar 0) * (ofVar $ pvar 0)

-- | CNOT gate
cxgate :: (Eq g, Num g) => Pathsum g
cxgate = Pathsum 0 [ivar 0, ivar 1] [] 0 [x0, x0+x1]
  where x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1

-- | CZ gate
czgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
czgate = Pathsum 0 [ivar 0, ivar 1] [] p [x0, x1]
  where p = lift $ x0 * x1
        x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1

-- | Toffoli gate
ccxgate :: (Eq g, Num g) => Pathsum g
ccxgate = Pathsum 0 [ivar 0, ivar 1, ivar 2] [] 0 [x0, x1, x2 + x0*x1]
  where x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1
        x2 = ofVar $ ivar 2

-- | CCZ gate
cczgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
cczgate = Pathsum 0 [ivar 0, ivar 1, ivar 2] [] p [x0, x1, x2]
  where p = lift $ x0 * x1 * x2
        x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1
        x2 = ofVar $ ivar 2

-- | k-control Toffoli gate
mctgate :: (Eq g, Num g) => Int -> Pathsum g
mctgate k = Pathsum 0 ivars [] 0 (controls ++ [t + foldr (*) 1 controls])
  where ivars    = [ivar i | i <- [0..k]]
        controls = [ofVar (ivar i) | i <- [0..k-1]]
        t        = ofVar $ ivar k

-- | n-qubit R_z gate
rzNgate :: (Eq g, Abelian g, Dyadic g) => g -> Int -> Pathsum g
rzNgate theta k = Pathsum 0 ivars [] p controls
  where ivars    = [ivar i | i <- [0..k-1]]
        controls = [ofVar (ivar i) | i <- [0..k-1]]
        p        = scale theta (lift $ foldr (*) 1 controls)

-- | SWAP gate
swapgate :: (Eq g, Num g) => Pathsum g
swapgate = Pathsum 0 [ivar 0, ivar 1] [] 0 [x1, x0]
  where x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1

-- | CH gate
chgate :: (Eq g, Abelian g, Dyadic g) => Pathsum g
chgate = Pathsum 1 [ivar 0, ivar 1] [pvar 0] p [x1, x2 + x1*x2 + x1*y]
  where p = distribute (-half*half) (1 + x1) +
            distribute half (lift $ (1 + x1) * y) +
            (lift $ x1 * x2 * y)
        x1 = ofVar $ ivar 0
        x2 = ofVar $ ivar 1
        y = ofVar $ pvar 0

{----------------------------
 Applicative style
 ----------------------------}

-- | apply an X gate
applyX :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyX i sop = sop { outVals = outVals' }
  where outVals' = over (ix i) (+ 1) $ outVals sop

-- | apply a Z gate
applyZ :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyZ i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute 1 ((outVals sop)!!i)

-- | apply a Y gate
applyY :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyY i sop = sop { phasePoly = phasePoly', outVals = outVals' }
  where outVals'   = over (ix i) (+ 1) $ outVals sop
        phasePoly' = phasePoly sop + distribute 1 ((outVals sop)!!i) + constant half

-- | apply an S gate
applyS :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyS i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute half ((outVals sop)!!i)

-- | apply an Sdg gate
applySdg :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applySdg i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute (-half) ((outVals sop)!!i)

-- | apply a T gate
applyT :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyT i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute (half*half) ((outVals sop)!!i)

-- | apply a Tdg gate
applyTdg :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyTdg i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute (-half*half) ((outVals sop)!!i)

-- | apply an Rk gate
applyRk :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyRk k i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute angle ((outVals sop)!!i)
        angle      = fromDyadic $ dyadic 1 k

-- | apply an Rz gate
applyRz :: (Eq g, Abelian g, Dyadic g) => g -> Int -> Pathsum g -> Pathsum g
applyRz theta i sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute theta ((outVals sop)!!i)

-- | apply an H gate
applyH :: (Eq g, Abelian g, Dyadic g) => Int -> Pathsum g -> Pathsum g
applyH i sop0 = sop { sde = sde',
                      pathVars = pathVars',
                      phasePoly = phasePoly',
                      outVals = outVals' }
  where (v, sop)   = newPVar sop0
        sde'       = 1 + sde sop
        pathVars'  = pathVars sop ++ [v]
        phasePoly' = phasePoly sop + distribute 1 (((outVals sop)!!i) * (ofVar v))
        outVals'   = set (ix i) (ofVar v) $ outVals sop
              

-- | apply a CZ gate
applyCZ :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyCZ i j sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute 1 (outI * outJ)
        outI       = (outVals sop)!!i
        outJ       = (outVals sop)!!j

-- | apply a CX gate
applyCX :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applyCX i j sop = sop { outVals = outVals' }
  where outVals' = over (ix j) (+ (outVals sop)!!i) $ outVals sop

-- | apply a CCZ gate
applyCCZ :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Int -> Pathsum g -> Pathsum g
applyCCZ i j k sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute 1 (outI * outJ * outK)
        outI       = (outVals sop)!!i
        outJ       = (outVals sop)!!j
        outK       = (outVals sop)!!k

-- | apply a CCX gate
applyCCX :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Int -> Pathsum g -> Pathsum g
applyCCX i j k sop = sop { outVals = outVals' }
  where outVals' = over (ix k) (+ outI * outJ) $ outVals sop
        outI     = (outVals sop)!!i
        outJ     = (outVals sop)!!j

-- | apply a Swap gate
applySwap :: (Eq g, Abelian g, Dyadic g) => Int -> Int -> Pathsum g -> Pathsum g
applySwap i j sop = sop { outVals = outVals' }
  where outVals' = set (ix i) outJ $ set (ix j) outI $ outVals sop
        outI     = (outVals sop)!!i
        outJ     = (outVals sop)!!j

-- | apply a multiply controlled Toffoli gate
applyMCT :: (Eq g, Abelian g, Dyadic g) => [Int] -> Int -> Pathsum g -> Pathsum g
applyMCT xs t sop = sop { outVals = outVals' }
  where outVals'  = over (ix t) (+ products) $ outVals sop
        products  = foldr (*) 1 (map ((outVals sop)!!) xs)

-- | apply a multiply controlled Rz gate
applyMCRz :: (Eq g, Abelian g, Dyadic g) => g -> [Int] -> Pathsum g -> Pathsum g
applyMCRz theta xs sop = sop { phasePoly = phasePoly' }
  where phasePoly' = phasePoly sop + distribute (theta) products
        products   = foldr (*) 1 (map ((outVals sop)!!) xs)

{----------------------------
 Channels
 ----------------------------}

-- | Choi matrix of computational basis measurement
measureChoi :: (Eq g, Abelian g) => Pathsum g
measureChoi = Pathsum 2 [ivar 0, ivar 1] [pvar 0] (lift $ y * (x0 + x1)) [x0, x1]
  where x0 = ofVar $ ivar 0
        x1 = ofVar $ ivar 1
        y  = ofVar $ pvar 0

-- | CPM operator of computational basis measurement
--measure :: (Eq g, Abelian g) => Pathsum g
--measure = unChoi measureChoi

{----------------------------
 Bind, unbind, and subst
 ----------------------------}
-- | Bind some collection of free variables in a path sum
bind :: (Foldable f, Eq g, Abelian g) => f Var -> Pathsum g -> Pathsum g
bind = flip (foldr go)
  where go x sop =
          let v = x { vtype = IVar } in
            sop { inVals = inVals sop ++ [v],
                  phasePoly = subst x (ofVar v) (phasePoly sop),
                  outVals = map (subst x (ofVar v)) (outVals sop) }

-- | Close a path sum by binding all free variables
close :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
close sop = bind (freeVars sop) sop

-- | Unbind (instantiate) some collection of inputs
unbind :: (Foldable f, Eq g, Abelian g) => f Var -> Pathsum g -> Pathsum g
unbind = flip (foldr go)
  where go x sop =
          let v = x { vtype = FVar } in
            sop { inVals = inVals sop \\ [x],
                  phasePoly = subst x (ofVar v) (phasePoly sop),
                  outVals = map (subst x (ofVar v)) (outVals sop) }

-- | Open a path sum by instantiating all inputs
open :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
open sop = unbind (inVals sop) sop

-- | Substitute a monomial with a symbolic Boolean expression throughout
--
--   This is generally not a very safe thing to do. Convenience for certain
--   local transformations
substitute :: (Eq g, Abelian g) => [Var] -> SBool Var -> Pathsum g -> Pathsum g
substitute xs p sop = sop { phasePoly = substMonomial xs p (phasePoly sop),
                            outVals   = map (substMonomial xs p) (outVals sop) }

-- | Rename all input and path variables to be canonical
inCanon :: (Eq g, Abelian g) => Int -> Int -> Pathsum g -> Pathsum g
inCanon ishift pshift sop = sop { inVals    = ivars,
                                  pathVars  = pvars,
                                  phasePoly = substMany sub (phasePoly sop),
                                  outVals   = map (substMany sub) (outVals sop) }
  where ivars   = [ivar (i + ishift) | i <- [0..length (inVals sop) - 1]]
        pvars   = [pvar (p + pshift) | p <- [0..length (pathVars sop) - 1]]
        sub v   = Map.findWithDefault (ofVar v) v nameMap
        nameMap = Map.fromList $ (zip (inVals sop) (map ofVar ivars)) ++
                                 (zip (pathVars sop) (map ofVar pvars))

-- | Allocate a new path variable
newPVar :: (Eq g, Abelian g) => Pathsum g -> (Var, Pathsum g)
newPVar sop = case v `elem` (pathVars sop) of
  False -> (v, sop)
  True  -> (v, inCanon 0 0 sop)
  where v = pvar (length $ pathVars sop)

{----------------------------
 Operators
 ----------------------------}

-- | Return the dual of a path sum
dualize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
dualize sop = inSOP .> midSOP .> outSOP
  where inSOP  = tensor (identity n) (etaN m)
        midSOP = tensor (tensor (identity n) sop) (identity m)
        outSOP = tensor (epsilonN n) (identity m)
        n      = outDeg sop
        m      = inDeg sop

-- | Return the (column) vectorized path sum. By convention we place the inputs
--   first (i.e. f : A -> B becomes vectorize f : A* \otimes B)
vectorize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
vectorize sop = etaN (inDeg sop) .> tensor (identity $ inDeg sop) sop

-- | Return the (row) vectorized path sum. By convention we place the outputs
--   first (i.e. f : A -> B becomes vectorize f : A* \otimes B)
covectorize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
covectorize sop = tensor (identity $ outDeg sop) sop .> epsilonN (outDeg sop)

-- | Take the conjugate (c.f., lower star) of a path sum
conjugate :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
conjugate sop = sop { phasePoly = (-(phasePoly sop)) }

-- | Take the dagger of a path sum
dagger :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
dagger = conjugate . dualize

-- | Trace a square morphism. Throws an error if the input and outputs are not
--   the same size
trace :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
trace sop
  | m /= n    = error "Can't trace a non-square operator"
  | otherwise = etaN n .> tensor (identity n) sop .> epsilonN n
  where m = inDeg sop
        n = outDeg sop

-- | Trace out the first qubit. Throws an error if the input is a vector
ptrace :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
ptrace sop
  | m < 1 || n < 1 = error "missing input or output"
  | otherwise = tensor eta (identity $ m-1) .>
                tensor (identity 1) sop .>
                tensor epsilon (identity $ n-1)
  where m = inDeg sop
        n = outDeg sop

-- | Turn a pure state into a density matrix. Throws an error if the input is not
--   a column vector
densify :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
densify sop
  | inDeg sop /= 0 = error "Can't densify an operator"
  | otherwise      = dagger sop .> sop

-- | Turn a (single-qubit) Choi matrix into a CPM-style linear operator
unChoi :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
unChoi sop
  | inDeg sop /= 2  = error "Only single-qubit channels currently supported"
  | outDeg sop /= 2 = error "Only single-qubit channels currently supported"
  | otherwise       = tensor eta swapgate .>
                      tensor (identity 1) (tensor sop $ identity 1) .>
                      tensor swapgate epsilon

-- | Turn a unitary operator into a channel. That is, f becomes f_* \otimes f
channelize :: (Eq g, Abelian g) => Pathsum g -> Pathsum g
channelize sop = tensor (conjugate sop) sop

-- | Compose two path sums in parallel. Can cause variable capture
tensorUnsafe :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
tensorUnsafe sop sop' = Pathsum sde' inVals' pathVars' phasePoly' outVals'
  where sde'       = (sde sop) + (sde sop')
        inVals'    = (inVals sop) ++ (inVals sop')
        pathVars'  = (pathVars sop) ++ (pathVars sop')
        phasePoly' = (phasePoly sop) + (phasePoly sop')
        outVals'   = (outVals sop) ++ (outVals sop')

-- | Compose two path sums in parallel
tensor :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
tensor sop sop'
  | intersect vs vs' == [] = tensorUnsafe sop sop'
  | otherwise              = tensorUnsafe s s'
  where vs  = inVals sop ++ pathVars sop
        vs' = inVals sop' ++ pathVars sop'
        s   = inCanon 0 0 sop
        s'  = inCanon (length $ inVals sop) (length $ pathVars sop) sop'

-- | Compose two path sums in sequence. Does not do any checks
timesUnsafe :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
timesUnsafe sop sop' = Pathsum sde' inVals' pathVars' phasePoly' outVals'
  where sde'       = (sde sop) + (sde sop')
        inVals'    = inVals sop
        pathVars'  = (pathVars sop) ++ (pathVars sop')
        phasePoly' = (phasePoly sop) + (substMany sub $ phasePoly sop')
        outVals'   = (map (substMany sub) $ outVals sop')
        sub v      = Map.findWithDefault (ofVar v) v nameMap
        nameMap    = Map.fromList $ (zip (inVals sop') (outVals sop))

-- | Compose two path sums in sequence. Throws an error if the dimensions are
--   not compatible.
times :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
times sop sop'
  | outDeg sop /= inDeg sop' = error "Incompatible dimensions"
  | intersect vs vs' == []   = timesUnsafe sop sop'
  | otherwise                = timesUnsafe s s'
  where vs  = pathVars sop
        vs' = pathVars sop'
        s   = inCanon 0 0 sop
        s'  = inCanon (length $ inVals sop) (length $ pathVars sop) sop'

-- | Left-to-right composition
(.>) :: (Eq g, Abelian g) => Pathsum g -> Pathsum g -> Pathsum g
(.>) = times

infixr 5 .>

-- | Scale the normalization factor
renormalize :: Int -> Pathsum g -> Pathsum g
renormalize k sop = sop { sde = sde sop + k }

{--------------------------
 Type class instances
 --------------------------}
  
instance (Eq g, Abelian g) => Semigroup (Pathsum g) where
  (<>) = tensor

instance (Eq g, Abelian g) => Monoid (Pathsum g) where
  mempty  = Pathsum 0 [] [] 0 []
  mappend = tensor

instance Functor Pathsum where
  fmap g sop = sop { phasePoly = cast g (phasePoly sop) }

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
  case vtype v' of
    PVar -> return (v, v', p')
    _    -> mzero

-- | Instances of the HH rule with a linear substitution
matchHHLinear :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHLinear sop = do
  (v, p)   <- filter ((<= 1) . degree . snd) $ matchHH sop
  (v', p') <- solveForX p
  case vtype v' of
    PVar -> return (v, v', p')
    _    -> mzero

-- | Instances of the HH rule with only internal substitutions
matchHHInternal :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHInternal sop = do
  (v, p)   <- matchHH sop
  (v', p') <- filter ((flip elem) (internalPaths sop) . fst) $ solveForX p
  case vtype v' of
    PVar -> return (v, v', p')
    _    -> mzero

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
  case (vtype v, p') of
    (_, 0)    -> mzero
    (PVar, p) -> return (v, ofVar v + p')
    _         -> mzero
  
{--------------------------
 Pattern synonyms
 --------------------------}

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
pattern Linear :: Eq g => Var -> SBool Var -> Pathsum g
pattern Linear v p <- (matchVar -> (v, p):_)

{--------------------------
 Applying reductions
 --------------------------}

-- | Apply an elim rule. Does not check if the instance is valid
applyElim :: Var -> Pathsum g -> Pathsum g
applyElim v sop = sop { sde = sde', pathVars = pathVars' }
  where sde'      = (sde sop) - 2
        pathVars' = (pathVars sop) \\ [v]

-- | Apply a (solvable) HH rule. Does not check if the instance is valid
applyHHSolved :: (Eq g, Abelian g) => Var -> Var -> SBool Var -> Pathsum g -> Pathsum g
applyHHSolved u v p sop = sop { sde = sde',
                                pathVars = pathVars',
                                phasePoly = phasePoly',
                                outVals = outVals' }
  where sde'       = (sde sop) - 2
        pathVars'  = (pathVars sop) \\ [u,v]
        phasePoly' = subst v p . remVar u $ phasePoly sop
        outVals'   = map (subst v p) $ outVals sop

-- | Apply an (\omega\) rule. Does not check if the instance is valid
applyOmega :: (Eq g, Abelian g, Dyadic g) => Var -> SBool Var -> Pathsum g -> Pathsum g
applyOmega v p sop = sop { sde = sde',
                           pathVars = pathVars',
                           phasePoly = phasePoly' }
  where sde'       = (sde sop) - 1
        pathVars'  = (pathVars sop) \\ [v]
        phasePoly' = const + quot + remVar v (phasePoly sop)
        const      = constant (fromDyadic $ dyadic 1 2)
        quot       = distribute (fromDyadic $ dyadic 3 1) (lift p)

-- | Apply a var rule. Does not check if the instance is valid
applyVar :: (Eq g, Abelian g) => Var -> SBool Var -> Pathsum g -> Pathsum g
applyVar v p sop = sop { phasePoly = phasePoly', outVals = outVals' }
  where phasePoly' = subst v p $ phasePoly sop
        outVals'   = map (subst v p) $ outVals sop

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
  Linear v p -> applyVar v p sop
  _          -> sop

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
  HHSolved y z p -> grind $ applyHHSolved y z p sop
  Omega y p      -> grind $ applyOmega y p sop
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

-- | Checks identity by checking inputs iteratively
isIdentity :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Bool
isIdentity sop
  | isTrivial sop = True
  | otherwise     = case inDeg sop of
      0 -> False
      i -> let p0 = (grind $ identity (i-1) <> ofKet [0] .> sop .> identity (i-1) <> ofBra [0])
               p1 = (grind $ identity (i-1) <> ofKet [1] .> sop .> identity (i-1) <> ofBra [1])
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
