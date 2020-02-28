{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Pathsum
Description : Sum-over-paths representation for simulation & verification
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Simulation.Pathsum where

import Data.Proxy
import Data.Type.Nat
import Data.Fin
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vec.Lazy (Vec(..))
import qualified Data.Vec.Lazy as V

import qualified Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear

{-----------------------------------
 Variables
 -----------------------------------}

-- | Variables are either input variables or path variables. The distinction
--   is due to the binding structure of our pathsum representation, and moreover
--   improves readability
data Var = IVar Integer | PVar Integer deriving (Eq, Ord)

instance Show Var where
  show (IVar i) = Unicode.sub "x" i
  show (PVar i) = Unicode.sub "y" i

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

{-----------------------------------
 Type classes
 -----------------------------------}

-- | Type class for symbolic data types supporting monotonic variable shifts
class Eq v => Shift v a | a -> v where
  shift :: (v -> v) -> a -> a

instance Ord v => Shift v (Multilinear v r repr) where
  shift = renameMonotonic

instance Shift v a => Shift v (Vec n a) where
  shift f = V.map (shift f)

-- | Type class for symbolic data types supporting substitution of Boolean polynomials
class Eq v => Subst v a | a -> v where
  subst    :: (v -> BoolPoly v) -> a -> a
  substVar :: v -> BoolPoly v -> a -> a
  -- | Default implementations
  substVar v p = subst (\v' -> if v == v' then p else ofVar v')

instance (Ord v, Eq r, ZModule r) => Subst v (PseudoBool v r) where
  subst = substMany

instance Subst v a => Subst v (Vec n a) where
  subst f = V.map (subst f)

-- | Type class for symbolic monoids with a conditional operation. In particular,
--
--     @ 'substVar' v '1' ('ite' v a b) == a @
--     @ 'substVar' v '0' ('ite' v a b) == b @
class Conditional v a where
  ite :: v -> a -> a -> a

instance (Ord v, Eq r, Num r) => Conditional v (PseudoBool v r) where
  ite v p q = q + (ofVar v)*(p - q)

instance Conditional v a => Conditional v (Vec n a) where
  ite v a b = V.zipWith (ite v) a b

class Exponential r where
  ee :: DyadicRational -> r

{-----------------------------------
 Coefficient rings
 -----------------------------------}

-- | The (multiplicative) group of complex numbers \(\frac{1}{\sqrt{2}} e^{2\pi i P}\)
--   where \(P\) is a Dyadic polynomial
data ScaledDyadicExp = SDE !Integer !(PseudoBool Var DMod2)
  deriving (Eq, Ord)

instance Show ScaledDyadicExp where
  show (SDE 0 p) = Unicode.e ++ "^" ++ Unicode.pi ++ Unicode.i ++ "{" ++ show p ++ "}"
  show (SDE i p) = "1/" ++ Unicode.sup Unicode.rt2 i ++ show (SDE 0 p)

instance Num ScaledDyadicExp where
  _s + _t                 = error "Cannot sum scaled dyadics"
  (SDE i p) * (SDE i' p') = SDE (i+i') (p+p')
  negate (SDE i p)        = SDE i (p + 1)
  abs                     = error "Cannot take abs"
  signum                  = error "Cannot signum"
  fromInteger 1           = SDE 0 $ constant 2
  fromInteger _           = error "Cannot construct non-unit integers"

instance Shift Var ScaledDyadicExp where
  shift f (SDE i p) = SDE i (shift f p)

instance Subst Var ScaledDyadicExp where
  subst f (SDE i p) = SDE i (subst f p)

instance Conditional Var ScaledDyadicExp where
  ite v (SDE i p) (SDE i' p')
    | i == i'   = SDE i (ite v p p')
    | otherwise = error "Operands to 'ite' do not have same normalization factor"

instance TwoRegular ScaledDyadicExp where
  fromDyadic (Dy 1 n) = SDE (fromIntegral n) 0
  fromDyadic (Dy _ n) = error "Cannot construct non-unit scalars"

instance Exponential ScaledDyadicExp where
  ee d = SDE 0 (constant $ fromDyadic d)

{-----------------------------------
 Path sums
 -----------------------------------}

-- | Type of symbolic basis states
type SState = BoolPoly Var

-- | A symbolic 'm' by 'n' matrix over a ring 'r' represented as a sum-over-paths
data Pathsum (m :: Nat) (n :: Nat) r = Pathsum {
  branches  :: !Integer,       -- ^ the number of branches
  amplitude :: !r,             -- ^ the amplitude of a given branch
  state     :: !(Vec n SState) -- ^ the output state of a given branch
  }

instance (Eq r, Num r, Show r, SNatI m, SNatI n) => Show (Pathsum m n r) where
  show pathsum = ip ++ su ++ am ++ st
    where am = if amplitude pathsum == 1 then "" else show $ amplitude pathsum
          st = V.foldMap (Unicode.ket . show) $ state pathsum
          ip = case inSize pathsum of
            0 -> ""
            1 -> Unicode.ket (ivar 0) ++ " " ++ Unicode.mapsto ++ " "
            2 -> Unicode.ket (ivar 0 ++ ivar 1) ++ " " ++ Unicode.mapsto ++ " "
            j -> Unicode.ket (ivar 0 ++ Unicode.dots ++ ivar (j-1)) ++ " " ++ Unicode.mapsto ++ " "
          su = case branches pathsum of
            0 -> ""
            1 -> Unicode.sum ++ "[" ++ pvar 0 ++ "]"
            2 -> Unicode.sum ++ "[" ++ pvar 0 ++ pvar 1 ++ "]"
            j -> Unicode.sum ++ "[" ++ pvar 0 ++ Unicode.dots ++ pvar (j-1) ++ "]"

-- | Convenience type for single qubit operations
type SingleQubitOp r = Pathsum Nat1 Nat1 r

-- | Convenience type for two qubit operations
type TwoQubitOp r = Pathsum Nat2 Nat2 r

-- | Convenience type for "kets"
type Ket n r = Pathsum Nat0 n r

-- | Convenience type for "bras"
type Bra m r = Pathsum m Nat0 r

{----------------------------
 Accessors
 ----------------------------}

-- | The number of inputs
inSize :: forall m n r. SNatI m => Pathsum m n r -> Integer
inSize _ = reflectToNum (Proxy :: Proxy m)

-- | The number of outputs
outSize :: forall m n r. SNatI n => Pathsum m n r -> Integer
outSize _ = reflectToNum (Proxy :: Proxy n)

-- | Retrieve the internal path variables
internalVars :: SNatI n => Pathsum m n r -> Set Var
internalVars sop = Set.difference (Set.fromList $ map PVar [0..branches sop]) outVars
  where outVars = Set.unions $ V.map vars (state sop)

{----------------------------
 Constructors
 ----------------------------}

-- | The identity pathsum
identity :: (Num r, SNatI n) => Pathsum n n r
identity = Pathsum 0 1 (V.map (ofVar . IVar . toInteger) V.universe)

-- | A computational basis state
classical :: Num r => Vec n FF2 -> Ket n r
classical = Pathsum 0 1 . V.map constant

-- | A fresh, 0-valued ancilla
fresh :: Num r => Ket Nat1 r
fresh = Pathsum 0 1 $ V.singleton 0

-- | Initialize a fresh ancilla
initialize :: Num r => FF2 -> Ket Nat1 r
initialize = Pathsum 0 1 . V.singleton . constant

-- | X gate
xgate :: Num r => Pathsum Nat1 Nat1 r
xgate = Pathsum 0 1 $ V.singleton (1 + (ofVar $ IVar 0))

-- | X gate
zgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat1 Nat1 r
zgate = Pathsum 0 (ite (IVar 0) (ee $ dyadic 1 0) 1) $ V.singleton (ofVar $ IVar 0)

--projector :: Num r => Vec n FF2 -> Pathsum n n r
--projector = dagger . ket

{----------------------------
 Composition
 ----------------------------}

-- | Add two path sums
plus :: (TwoRegular r, Conditional Var r, Shift Var r) =>
  Pathsum m n r -> Pathsum m n r -> Pathsum m n r
plus (Pathsum b a s) (Pathsum b' a' s') = Pathsum b'' a'' s''
  where sub = shiftP b
        b'' = b + b' + 1
        a'' =
          let ascale  = a * (fromDyadic (dyadic 1 (fromIntegral b')))
              a'scale = a' * (fromDyadic (dyadic 1 (fromIntegral b)))
          in
            ite (PVar $ b''-1) ascale (shift sub a'scale)
        s'' = ite (PVar $ b''-1) s (shift sub s')

-- | Compose two path sums in parallel
tensor :: (Num r, Shift Var r, SNatI m) =>
  Pathsum m n r -> Pathsum m' n' r -> Pathsum (Plus m m') (Plus n n') r
tensor tmp@(Pathsum b a s) (Pathsum b' a' s') = Pathsum b'' a'' s''
  where sub = shiftAll (inSize tmp) b
        b'' = b+b'
        a'' = a * (shift sub a')
        s'' = (V.++) s (shift sub s')

-- | Functional composition
compose :: (Num r, Subst Var r, Shift Var r, SNatI k) =>
  Pathsum m k r -> Pathsum k n r -> Pathsum m n r
compose (Pathsum b a s) (Pathsum b' a' s') = Pathsum b'' a'' s''
  where shft = shiftP b
        sub  =
          let f i = Map.insert (IVar $ toInteger i) in
            \v -> Map.findWithDefault (ofVar v) v $ V.ifoldr f Map.empty s
        b''  = b + b'
        a''  = a * subst sub (shift shft a')
        s''  = subst sub (shift shft s')

{-
restrict :: (Eq a, Num a) => SOP a -> Map ID Bool -> SOP a
restrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if (simplify x') == (simplify $ constant (bra!x))
              then sop
              else error "Zero amplitude on target state" --SOP 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> error $ "Can't reify " ++ (show $ constant (bra!x) + x') ++ " = 0"
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

tryRestrict :: (Eq a, Num a) => SOP a -> Map ID Bool -> SOP a
tryRestrict sop bra = foldl' f sop $ Map.keys bra
  where f sop x =
          let x' = (outVals sop)!x in
            if degree x' < 1
            then
              if x' == constant (bra!x)
              then sop
              else SOP 0 Map.empty [] zero Map.empty
            else
              case find ((`elem` (map pathVar $ pathVars sop)) . fst) $ solveForX (constant (bra!x) + x') of
                Nothing        -> sop
                Just (y, psub) -> sop { pathVars = pathVars sop \\ [read $ tail y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

restrictGeneral :: (Eq a, Num a) => SOP a -> Map ID (Multilinear Bool) -> SOP a
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
      
instance (Eq a, Num a) => Semigroup (SOP a) where
  a <> b = compose a b

instance (Eq a, Num a) => Monoid (SOP a) where
  mempty  = identity0
  mappend = compose

{- Implementations -}

newtype Z8 = Z8 { inject :: Int } deriving (Eq)

instance Show Z8 where
  show (Z8 x) = show x

instance Num Z8 where
  (Z8 x) + (Z8 y) = Z8 $ (x + y) `mod` 8
  (Z8 x) * (Z8 y) = Z8 $ (x * y) `mod` 8
  negate (Z8 x)   = Z8 $ 8 - x
  abs (Z8 x)      = Z8 $ x `mod` 8
  signum (Z8 x)   = Z8 $ signum x
  fromInteger i   = Z8 $ fromIntegral $ i `mod` 8

toSOPWithHints :: [ID] -> Primitive -> SOP Z8
toSOPWithHints vars gate = case gate of
  H x      -> init { pathVars = [0],
                     sde = s + 1,
                     poly = p + ofTerm (fromInteger 4) [x, "p0"],
                     outVals = Map.insert x (ofVar "p0") outv }
  X x      -> init { outVals = Map.adjust (+ one) x outv }
  Y x      -> init { poly = p + (constant $ fromInteger 2) + (ofTerm (fromInteger 4) [x]),
                     outVals = Map.adjust (+ one) x outv }
  Z x      -> init { poly = p + (ofTerm (fromInteger 4) [x]) }
  CNOT x y -> init { outVals = Map.adjust (+ (ofVar x)) y outv }
  S x      -> init { poly = p + (ofTerm (fromInteger 2) [x]) }
  Sinv x   -> init { poly = p + (ofTerm (fromInteger 6) [x]) }
  T x      -> init { poly = p + (ofTerm (fromInteger 1) [x]) }
  Tinv x   -> init { poly = p + (ofTerm (fromInteger 7) [x]) }
  Swap x y -> init { outVals = Map.insert x (outv!y) $ Map.insert y (outv!x) outv }
  where init@(SOP s inv pathv p outv) = identity vars

toSOP :: Primitive -> SOP Z8
toSOP gate = case gate of
  H x      -> toSOPWithHints [x] gate
  X x      -> toSOPWithHints [x] gate
  Y x      -> toSOPWithHints [x] gate
  Z x      -> toSOPWithHints [x] gate
  CNOT x y -> toSOPWithHints [x,y] gate
  S x      -> toSOPWithHints [x] gate
  Sinv x   -> toSOPWithHints [x] gate
  T x      -> toSOPWithHints [x] gate
  Tinv x   -> toSOPWithHints [x] gate
  Swap x y -> toSOPWithHints [x,y] gate


circuitSOPWithHints :: [ID] -> [Primitive] -> SOP Z8
circuitSOPWithHints vars circuit = foldMap (toSOPWithHints vars) circuit

circuitSOP :: [Primitive] -> SOP Z8
circuitSOP circuit = foldMap toSOP circuit

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

isClosed :: (Eq a, Num a) => SOP a -> Bool
isClosed = (< 1) . degree . poly

{- Folds over paths -}

foldPaths :: (Eq a, Num a) => (SOP a -> b) -> (b -> b -> b) -> SOP a -> b
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

foldReduce :: (Eq a, Fin a) => (SOP a -> b) -> (b -> b -> b) -> SOP a -> b
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

foldReduceFull :: (Show a, Eq a, Fin a) => (SOP a -> b) -> (b -> b -> b) -> SOP a -> b
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

expandPaths :: (Eq a, Num a) => SOP a -> [SOP a]
expandPaths = foldPaths (\x -> [x]) (++)

amplitudesMaybe :: SOP Z8 -> Maybe (Map (Map ID (Multilinear Bool)) DOmega)
amplitudesMaybe sop = foldReduce f g sop
  where f sop = if isClosed sop then
                    Just $ Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
                  else
                    Nothing
        g = liftM2 (Map.unionWith (+))

amplitudes :: SOP Z8 -> Map (Map ID (Multilinear Bool)) DOmega
amplitudes sop = foldReduceFull f g sop
  where f sop = Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
        g = Map.unionWith (+)

{- Reduction -}

data Rule =
    Elim String
  | Omega String (Multilinear Bool)
  | HH String String (Multilinear Bool)
  | Case String String (Multilinear Bool) String (Multilinear Bool)

instance Show Rule where
  show (Elim x)         = "[Elim] " ++ x
  show (Omega x p)      = "[Omega] " ++ x ++ ", remainder: " ++ show p
  show (HH x y p)       = "[HH] " ++ x ++ ", " ++ y ++ " <- "  ++ show p
  show (Case x y p z q) = "[Case] " ++ x ++ ", " ++ y ++ " <- " ++ show p
                                         ++ ", " ++ z ++ " <- " ++ show q

class Num a => Fin a where
  order :: a -> Int

instance Fin Z8 where
  order (Z8 x) = (lcm x 8) `div` x

injectZ2 :: Fin a => a -> Maybe Bool
injectZ2 a = case order a of
  0 -> Just False
  2 -> Just True
  _ -> Nothing

toBooleanPoly :: (Eq a, Fin a) => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2 . simplify

axiomSimplify :: (Eq a, Fin a) => SOP a -> Maybe Int
axiomSimplify sop = msum . (map f) $ internalPaths sop
  where f i = if (pathVar i) `appearsIn` (poly sop) then Nothing else Just i

axiomHHStrict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHStrict sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop)
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomHHOutputRestricted :: (Eq a, Fin a) => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHOutputRestricted sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop) && degree p <= 1
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomSH3Strict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Multilinear Bool)
axiomSH3Strict sop = msum . (map f) $ internalPaths sop
  where f i =
          let p' = factorOut (pathVar i) $ (poly sop) - (ofTerm 2 [pathVar i]) in
            toBooleanPoly p' >>= \q -> Just (i, q)

axiomUnify :: (Eq a, Fin a) => SOP a -> Maybe (ID, Int, Multilinear Bool, Int, Multilinear Bool)
axiomUnify sop = msum . (map f) $ internal
  where internal   = internalPaths sop
        findSoln i = find (\(x, _) -> x == pathVar i) . solveForX
        f i        = do
          p'      <- return $ factorOut (pathVar i) $ poly sop
          (m, _)  <- find (\(m, a) -> monomialDegree m == 1 && order a == 4) . Map.toList . terms $ p'
          x       <- find (\v -> not (v == pathVar i)) $ monomialVars m
          p1      <- toBooleanPoly (p' - (ofTerm 2 [x]))
          msum . (map $ g p' i x p1) $ internal \\ [i]
        g p' i x p1 j = do
          p''       <- return $ factorOut (pathVar j) $ poly sop
          p2        <- toBooleanPoly (p'' - (constant (fromInteger 2)) - (ofTerm 6 [x]))
          (_, jsub) <- findSoln j (subst x zero p1)
          (_, isub) <- findSoln i (subst x one p2)
          return (x, i, isub, j, jsub)

axiomKill :: (Eq a, Fin a) => SOP a -> Maybe Int
axiomKill sop = msum . (map f) $ internalPaths sop
  where f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          if intersect (vars p'') (map pathVar $ pathVars sop) == []
            then Just i
            else Nothing

-- Single application of an axiom
applyRule :: (Eq a, Fin a) => SOP a -> Maybe (Rule, SOP a)
applyRule sop = case sop of
  (axiomSimplify -> Just rem) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem] }
    in
      Just (Elim $ pathVar rem, sop')
  (axiomHHStrict -> Just (rem, sub, eq)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem, sub],
                     poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
                     outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
    in
      Just (HH (pathVar rem) (pathVar sub) eq, sop')
  (axiomSH3Strict -> Just (rem, eq)) ->
    let sop' = sop { sde      = sde sop - 1,
                     pathVars = pathVars sop \\ [rem],
                     poly     = simplify $ one + distribute 6 eq + removeVar (pathVar rem) (poly sop) }
    in
      Just (Omega (pathVar rem) eq, sop')
  (axiomUnify     -> Just (x, i, isub, j, jsub)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [i, j],
                     poly     =
                       let xp = ofVar x
                           pi = subst (pathVar j) jsub . subst x zero . removeVar (pathVar i) $ poly sop
                           pj = subst (pathVar i) isub . subst x one  . removeVar (pathVar j) $ poly sop
                       in
                         simplify $ xp*pj + pi - xp*pi
                   }
    in
      Just (Case x (pathVar i) isub (pathVar j) jsub, sop')
  _ -> Nothing

-- Only performs linear substitutions. Useful for simplifying without increasing complexity
applyRuleOutputRestricted :: (Eq a, Fin a) => SOP a -> Maybe (Rule, SOP a)
applyRuleOutputRestricted sop = case sop of
  (axiomSimplify -> Just rem) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem] }
    in
      Just (Elim $ pathVar rem, sop')
  (axiomHHOutputRestricted -> Just (rem, sub, eq)) ->
    let sop' = sop { sde      = sde sop - 2,
                     pathVars = pathVars sop \\ [rem, sub],
                     poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
                     outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
    in
      Just (HH (pathVar rem) (pathVar sub) eq, sop')
  (axiomSH3Strict -> Just (rem, eq)) ->
    let sop' = sop { sde      = sde sop - 1,
                     pathVars = pathVars sop \\ [rem],
                     poly     = simplify $ one + distribute 6 eq + removeVar (pathVar rem) (poly sop) }
    in
      Just (Omega (pathVar rem) eq, sop')
  _ -> Nothing

{- Strategies -}

-- Applies reductions until a fixpoint is reached
reduce :: (Eq a, Fin a) => SOP a -> ([Rule], SOP a)
reduce sop = go ([], sop)
  where go (applied, sop) = case applyRule sop of
          Nothing           -> (reverse applied, sop)
          Just (rule, sop') -> go (rule:applied, sop')

-- Fully reduces a path sum for a given input and output state
evaluate :: (Eq a, Fin a) => SOP a -> Map ID Bool -> Map ID Bool -> ([Rule], SOP a)
evaluate sop ket bra = reduce $ restrict (ofKet ket <> sop) bra
-}
