{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-|
Module      : Concrete
Description : A concrete path sum for Clifford+Rz circuits
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.Pathsum.Concrete where

import Data.List
import qualified Data.Set as Set
import Data.Ratio
import Data.Semigroup
import Control.Monad (mzero, msum)
import Data.Maybe (maybeToList)

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
data Var = IVar !Integer | PVar !Integer deriving (Eq, Ord)

instance Show Var where
  show (IVar i) = U.sub "x" i
  show (PVar i) = U.sub "y" i

-- | Convenience function for the string representation of the 'i'th input variable
ivar :: Integer -> String
ivar = show . IVar

-- | Convenience function for the string representation of the 'i'th path variable
pvar :: Integer -> String
pvar = show . PVar

-- | Construct an integer shift for input variables
shiftI :: Integer -> (Var -> Var)
shiftI i = shiftAll i 0

-- | Construct an integer shift for path variables
shiftP :: Integer -> (Var -> Var)
shiftP j = shiftAll 0 j

-- | General shift. Constructs a substitution from shift values for I and P
shiftAll :: Integer -> Integer -> (Var -> Var)
shiftAll i j = go
  where go (IVar i') = IVar (i + i')
        go (PVar j') = PVar (j + j')

-- | Path sums of the form
--   \(\frac{1}{\sqrt{2}^k}\sum_{y\in\mathbb{Z}_2^m}e^{i\pi P(x, y)}|f(x, y)\rangle\)
data Pathsum g = Pathsum {
  sde       :: !Integer,
  inDeg     :: !Integer,
  outDeg    :: !Integer,
  pathVars  :: !Integer,
  phasePoly :: !(PseudoBoolean Var g),
  outVals   :: ![SBool Var]
  } deriving (Eq)

instance (Show g, Eq g, Periodic g, Real g) => Show (Pathsum g) where
  show sop = inputstr ++ scalarstr ++ sumstr ++ amplitudestr ++ statestr
    where inputstr = case inDeg sop of
            0 -> ""
            1 -> U.ket (ivar 0) ++ " " ++ U.mapsto ++ " "
            2 -> U.ket (ivar 0 ++ ivar 1) ++ " " ++ U.mapsto ++ " "
            j -> U.ket (ivar 0 ++ U.dots ++ ivar (j-1)) ++ " " ++ U.mapsto ++ " "
          scalarstr = case compare (sde sop) 0 of
            LT -> U.sup ("(" ++ U.rt2 ++ ")") (abs $ sde sop)
            EQ -> ""
            GT -> U.sup ("1/(" ++ U.rt2 ++ ")") (sde sop)
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

{----------------------------
 Constructors
 ----------------------------}

-- | Construct an 'n'-qubit identity operator
identity :: (Eq g, Num g) => Integer -> Pathsum g
identity n = Pathsum 0 n n 0 0 [ofVar (IVar i) | i <- [0..n-1]]

-- | Construct a ket
ket :: (Eq g, Num g) => [FF2] -> Pathsum g
ket xs = Pathsum 0 0 (fromIntegral $ length xs) 0 0 $ map constant xs

-- | Construct a bra
bra :: (Eq g, ZModule g) => [FF2] -> Pathsum g
bra xs = Pathsum 2 (fromIntegral $ length xs) 0 1 (lift $ y*(1 + p)) []
  where y = ofVar (PVar 0)
        p = foldr (*) 1 . map valF $ zip xs [0..]
        valF (val, i) = 1 + constant val + ofVar (IVar i)

-- | Initialize a fresh ancilla
initialize :: (Eq g, Num g) => FF2 -> Pathsum g
initialize b = ket [b]

{-# INLINE initialize #-}

-- | Dagger of initialize -- i.e. unnormalized post-selection
postselect :: (Eq g, ZModule g) => FF2 -> Pathsum g
postselect b = bra [b]

{-# INLINE postselect #-}

{----------------------------
 Constants
 ----------------------------}

-- | A fresh, 0-valued ancilla
fresh :: (Eq g, Num g) => Pathsum g
fresh = Pathsum 0 0 1 0 0 [0]

-- | X gate
xgate :: (Eq g, Num g) => Pathsum g
xgate = Pathsum 0 1 1 0 0 [1 + ofVar (IVar 0)]

-- | Z gate
zgate :: (Eq g, ZModule g) => Pathsum g
zgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = lift $ ofVar (IVar 0)

-- | Y gate
ygate :: (Eq g, ZModule g, TwoRegular g) => Pathsum g
ygate = Pathsum 0 1 1 0 p [1 + ofVar (IVar 0)]
  where p = constant half + (lift $ ofVar (IVar 0))

-- | S gate
sgate :: (Eq g, ZModule g, TwoRegular g) => Pathsum g
sgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = scale half (lift $ ofVar (IVar 0))

-- | T gate
tgate :: (Eq g, ZModule g, TwoRegular g) => Pathsum g
tgate = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = scale (half*half) (lift $ ofVar (IVar 0))

-- | R_k gate
rkgate :: (Eq g, ZModule g, TwoRegular g) => Int -> Pathsum g
rkgate k = Pathsum 0 1 1 0 p [ofVar (IVar 0)]
  where p = scale (fromDyadic $ dyadic 1 k) (lift $ ofVar (IVar 0))

-- | H gate
hgate :: (Eq g, ZModule g, TwoRegular g) => Pathsum g
hgate = Pathsum 1 1 1 1 p [ofVar (PVar 0)]
  where p = lift $ (ofVar $ IVar 0) * (ofVar $ PVar 0)

-- | CNOT gate
cxgate :: (Eq g, Num g) => Pathsum g
cxgate = Pathsum 0 2 2 0 0 [x0, x0+x1]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1

-- | SWAP gate
swapgate :: (Eq g, Num g) => Pathsum g
swapgate = Pathsum 0 2 2 0 0 [x1, x0]
  where x0 = ofVar $ IVar 0
        x1 = ofVar $ IVar 1

{----------------------------
 Composition
 ----------------------------}

-- | Attempt to add two path sums. Only succeeds if the resulting sum is balanced
--   and the dimensions match.
plusMaybe :: (Eq g, ZModule g) => Pathsum g -> Pathsum g -> Maybe (Pathsum g)
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

-- | Construct thesum of two path sums. Raises an error if the sums are incompatible
plus :: (Eq g, ZModule g) => Pathsum g -> Pathsum g -> Pathsum g
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

-- | Attempt to compose two path sums in sequence. Only succeeds if the dimensions
--   are compatible (i.e. if the out degree of the former is the in degree of the
--   latter)
timesMaybe :: (Eq g, ZModule g) => Pathsum g -> Pathsum g -> Maybe (Pathsum g)
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
          IVar i -> (outVals sop)!!(fromInteger i)
          _      -> ofVar x

-- | Compose two path sums in sequence. Throws an error if the dimensions are
--   not compatible
times :: (Eq g, ZModule g) => Pathsum g -> Pathsum g -> Pathsum g
times sop sop' = case timesMaybe sop sop' of
  Nothing    -> error "Incompatible path sum dimensions"
  Just sop'' -> sop''

-- | Scale the normalization factor
renormalize :: Integer -> Pathsum g -> Pathsum g
renormalize k (Pathsum a b c d e f) = Pathsum (a + k) b c d e f

{--------------------------
 Type class instances
 --------------------------}
  
instance (Eq g, Num g) => Semigroup (Pathsum g) where
  (<>) = tensor

instance (Eq g, Num g) => Monoid (Pathsum g) where
  mempty  = Pathsum 0 0 0 0 0 []
  mappend = tensor

instance (Eq g, ZModule g) => Num (Pathsum g) where
  (+)                          = plus
  (*)                          = (flip times)
  negate (Pathsum a b c d e f) = Pathsum a b c d (lift 1 + e) f
  abs (Pathsum a b c d e f)    = Pathsum a b c d (dropConstant e) f
  signum sop                   = sop
  fromInteger                  = identity

{--------------------------
 Reduction rules
 --------------------------}

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
  where go v = toBooleanPoly (divVar v $ phasePoly sop) >>= \p -> return (v, p)

-- | Solvable instances of the HH rule.
--   \(\dots(\sum_y (-1)^{y(z \oplus f)})\dots = \dots[z \gets f]\)
matchHHSolve :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHSolve sop = do
  (v, p)   <- matchHH sop
  (v', p') <- solveForX p
  case v' of
    PVar j -> return (v, v', p')
    _      -> mzero

-- | Instances of the HH rule with a linear substitution
matchHHLinear :: (Eq g, Periodic g) => Pathsum g -> [(Var, Var, SBool Var)]
matchHHLinear sop = do
  (v, p)   <- filter (\(_, p) -> degree p <= 1) $ matchHH sop
  (v', p') <- solveForX p
  return (v, v', p')

-- | Instances of the (\omega\) rule
matchOmega :: (Eq g, Periodic g, TwoRegular g) => Pathsum g -> [(Var, SBool Var)]
matchOmega sop = do
  v <- internalPaths sop
  p <- maybeToList . toBooleanPoly . addFactor v $ phasePoly sop
  return (v, p)
  where addFactor v p = constant (fromDyadic $ dyadic 1 1) + divVar v p

{--------------------------
 Pattern synonyms for reductions
 --------------------------}

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

-- | Pattern synonym for Omega instances
pattern Omega :: (Eq g, Periodic g, TwoRegular g) => Var -> SBool Var -> Pathsum g
pattern Omega v p <- (matchOmega -> (v, p):_)

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
applyHHSolved :: (Eq g, ZModule g) => Var -> Var -> SBool Var -> Pathsum g -> Pathsum g
applyHHSolved (PVar i) v p (Pathsum a b c d e f) = Pathsum a b c (d-1) e' f'
  where e' = renameMonotonic varShift . subst v p . remVar (PVar i) $ e
        f' = map (renameMonotonic varShift . subst v p) f
        varShift (PVar j)
          | j > i     = PVar $ j - 1
          | otherwise = PVar $ j
        varShift v = v

-- | Apply an (\omega\) rule. Does not check if the instance is valid
applyOmega :: (Eq g, ZModule g, TwoRegular g) => Var -> SBool Var -> Pathsum g -> Pathsum g
applyOmega (PVar i) p (Pathsum a b c d e f) = Pathsum (a-1) b c (d-1) e' f'
  where e' = renameMonotonic varShift $ p' + remVar (PVar i) e
        f' = map (renameMonotonic varShift) f
        p' = constant (fromDyadic $ dyadic 1 2) + scale (fromDyadic $ dyadic 3 1) (lift p)
        varShift (PVar j)
          | j > i     = PVar $ j - 1
          | otherwise = PVar $ j
        varShift v = v

{--------------------------
 Reduction procedures
 --------------------------}

-- | A complete normalization procedure for Clifford circuits. Originally described in
--   the paper M. Amy,
--   / Towards Large-Scaled Functional Verification of Universal Quantum Circuits /, QPL 2018.
grind :: (Eq g, Periodic g, ZModule g, TwoRegular g) => Pathsum g -> Pathsum g
grind sop = case sop of
  Elim y         -> grind $ applyElim y sop
  HHSolved y z p -> grind $ applyHHSolved y z p sop
  Omega y p      -> grind $ applyOmega y p sop
  _              -> sop

-- | Grinds a pathsum for a given input & output
evaluate :: (Eq g, Periodic g, ZModule g, TwoRegular g) => [FF2] -> Pathsum g -> [FF2] -> Pathsum g
evaluate o sop i = grind $ bra o <> sop <> ket i

{--------------------------
 Deprecated methods
 --------------------------}
{-
restrict :: (Eq a, Num a) => Pathsum a -> Map ID Bool -> Pathsum a
restrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if (simplify x') == (simplify $ constant (bra!x))
              then sop
              else error "Zero amplitude on target state" --Pathsum 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> error $ "Can't reify " ++ (show $ constant (bra!x) + x') ++ " = 0"
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

tryRestrict :: (Eq a, Num a) => Pathsum a -> Map ID Bool -> Pathsum a
tryRestrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if x' == constant (bra!x)
              then sop
              else Pathsum 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> sop
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

restrictGeneral :: (Eq a, Num a) => Pathsum a -> Map ID (Multilinear Bool) -> Pathsum a
restrictGeneral sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if (simplify x') == (simplify $ bra!x)
            then sop
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (bra!x + x') of
                Nothing        -> error $ "Can't reify " ++ (show $ bra!x + x') ++ " = 0"
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }
      
instance (Eq a, Num a) => Semigroup (Pathsum a) where
  a <> b = compose a b

instance (Eq a, Num a) => Monoid (Pathsum a) where
  mempty  = identity0
  mappend = compose

{- Simulation -}

newtype DyadicInt = D (Int, Int) deriving (Eq) -- NOTE: must be in lowest form
newtype DOmega    = DOmega (DyadicInt, DyadicInt, DyadicInt, DyadicInt) deriving (Eq)

instance Show DyadicInt where
  show (D (a,n)) = show a ++ "/2^" ++ show n

instance Num DyadicInt where
  (D (a,n)) + (D (b,m))
    | a == 0 = D (b,m)
    | b == 0 = D (a,n)
    | n == m = canonicalize $ D ((a + b) `div` 2, n-1)
    | otherwise =
      let n' = max n m in
        canonicalize $ D (a * 2^(n' - n) + b * 2^(n' - m), n')
  (D (a,n)) * (D (b,m)) = canonicalize $ D (a * b, n + m)
  negate (D (a,n)) = D (-a, n)
  abs (D (a,n))    = D (abs a, n)
  signum (D (a,n)) = D (signum a, 0)
  fromInteger i    = D (fromInteger i, 0)

canonicalize :: DyadicInt -> DyadicInt
canonicalize (D (a,n))
  | a == 0                  = D (0,0)
  | a `mod` 2 == 0 && n > 0 = canonicalize $ D (a `div` 2, n-1)
  | otherwise               = D (a,n)

instance Show DOmega where
  show (DOmega (a,b,c,d)) =
    show a ++ " + " ++
    show b ++ "*w + " ++
    show c ++ "*w^2 + " ++
    show d ++ "*w^3"

instance Num DOmega where
  DOmega (a,b,c,d) + DOmega (a',b',c',d') = DOmega (a+a',b+b',c+c',d+d')
  DOmega (a,b,c,d) * DOmega (a',b',c',d') = DOmega (a'',b'',c'',d'')
    where a'' = a*a' - b*d' - c*c' - d*b'
          b'' = a*b' + b*a' - c*d' - d*c'
          c'' = a*c' + b*b' + c*a' - d*d'
          d'' = a*d' + b*c' + c*b' + d*a'
  negate (DOmega (a,b,c,d)) = DOmega (-a,-b,-c,-d)
  abs    x = x -- N/A
  signum x = x -- N/A
  fromInteger i = DOmega (fromInteger i, D (0,0), D (0,0), D (0,0))

-- w^x
expZ8 :: Z8 -> DOmega
expZ8 (Z8 x) = case x `mod` 4 of
  0 -> DOmega (D (y,0), D (0,0), D (0,0), D (0,0))
  1 -> DOmega (D (0,0), D (y,0), D (0,0), D (0,0))
  2 -> DOmega (D (0,0), D (0,0), D (y,0), D (0,0))
  3 -> DOmega (D (0,0), D (0,0), D (0,0), D (y,0))
  where y = (-1)^(x `div` 4)

scaleD :: DyadicInt -> DOmega -> DOmega
scaleD x (DOmega (a,b,c,d)) = DOmega (x*a,x*b,x*c,x*d)

-- 1/sqrt(2)^i * w^x
scaledExp :: Int -> Z8 -> DOmega
scaledExp i (Z8 x)
  | i `mod` 2 == 0 = scaleD (D (1,i `div` 2)) (expZ8 $ Z8 x)
  | otherwise      = scaledExp (i+1) (Z8 $ mod (x-1) 8) + scaledExp (i+1) (Z8 $ mod (x+1) 8)

isClosed :: (Eq a, Num a) => Pathsum a -> Bool
isClosed = (< 1) . degree . poly

{- Folds over paths -}

foldPaths :: (Eq a, Num a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldPaths f g sop = case pathVars sop of
      []   -> f sop
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldPaths f g sop0) (foldPaths f g sop1)

foldReduce :: (Eq a, Fin a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldReduce f g sop = case pathVars sop of
      []   -> f sop
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldReduce f g . snd . reduce $ sop0) (foldReduce f g . snd . reduce $ sop1)

foldReduceFull :: (Show a, Eq a, Fin a) => (Pathsum a -> b) -> (b -> b -> b) -> Pathsum a -> b
foldReduceFull f g sop = case (pathVars sop, inputVars) of
      ([], []) -> f sop
      ([], x:xs) ->
        let sop0 = sop { poly = simplify . subst x zero $ poly sop,
                         outVals = Map.map (simplify . subst x zero) $ outVals sop }
            sop1 = sop { poly = simplify . subst x one $ poly sop,
                         outVals = Map.map (simplify . subst x one) $ outVals sop }
        in
          g (foldReduceFull f g . snd . reduce $ sop0) (foldReduceFull f g . snd . reduce $ sop1)
      (x:xs, _) ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          g (foldReduceFull f g . snd . reduce $ sop0) (foldReduceFull f g . snd . reduce $ sop1)
  where inputVars = foldr (\poly -> union (vars poly)) (vars $ poly sop) (Map.elems $ outVals sop)

expandPaths :: (Eq a, Num a) => Pathsum a -> [Pathsum a]
expandPaths = foldPaths (\x -> [x]) (++)

amplitudesMaybe :: Pathsum Z8 -> Maybe (Map (Map ID (Multilinear Bool)) DOmega)
amplitudesMaybe sop = foldReduce f g sop
  where f sop = if isClosed sop then
                    Just $ Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
                  else
                    Nothing
        g = liftM2 (Map.unionWith (+))

amplitudes :: Pathsum Z8 -> Map (Map ID (Multilinear Bool)) DOmega
amplitudes sop = foldReduceFull f g sop
  where f sop = Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
        g = Map.unionWith (+)

-}
