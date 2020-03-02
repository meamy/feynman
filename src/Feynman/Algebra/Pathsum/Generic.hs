{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Generic
Description : Sum-over-paths representation for simulation & verification
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Simulation.Pathsum.Generic where

import Data.Proxy
import Data.Type.Nat
--import Data.Fin
import Data.Set (Set)
import qualified Data.Set as Set
--import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vec.Lazy (Vec(..))
import qualified Data.Vec.Lazy as V

import qualified Feynman.Util.Unicode as Unicode
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear

{-----------------------------------
 Variables
 -----------------------------------}

-- | Variables are either input variables or path variables. The distinction
--   is due to the binding structure of our pathsum representation, and moreover
--   improves readability
data Var = IVar !Integer | PVar !Integer deriving (Eq, Ord)

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
class Ord v => Subst v a | a -> v where
  subst    :: (v -> SBool v) -> a -> a
  substVar :: v -> SBool v -> a -> a
  -- | Default implementations
  substVar v p = subst (\v' -> if v == v' then p else ofVar v')

instance (Ord v, Eq r, ZModule r) => Subst v (PseudoBoolean v r) where
  subst = substMany

instance Subst v a => Subst v (Vec n a) where
  subst f = V.map (subst f)

-- | Type class for symbolic monoids with a conditional operation. In particular,
--
--     @ 'substVar' v '1' ('ite' v a b) == a @
--     @ 'substVar' v '0' ('ite' v a b) == b @
class Conditional v a where
  ite :: SBool v -> a -> a -> a

instance (Ord v, Eq r, ZModule r) => Conditional v (PseudoBoolean v r) where
  ite c p q = q + (lift c)*(p - q)

instance Conditional v a => Conditional v (Vec n a) where
  ite c a b = V.zipWith (ite c) a b

class Exponential r where
  ee :: DyadicRational -> r

{-----------------------------------
 Coefficient rings
 -----------------------------------}

-- | The (multiplicative) group of complex numbers \(\frac{1}{\sqrt{2}} e^{2\pi i P}\)
--   where \(P\) is a Dyadic polynomial
data ScaledDyadicExp = SDE !Integer !(PseudoBoolean Var DMod2)
  deriving (Eq, Ord)

instance Show ScaledDyadicExp where
  show (SDE 0 p) = Unicode.e ++ "^" ++ Unicode.i ++ Unicode.pi ++ "{" ++ show p ++ "}"
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
  fromDyadic (Dy 1 n) = SDE (fromIntegral (2*n)) 0
  fromDyadic (Dy _ n) = error "Cannot construct non-unit scalars"

instance Exponential ScaledDyadicExp where
  ee d = SDE 0 (constant $ fromDyadic d)

{-----------------------------------
 Path sums
 -----------------------------------}

-- | Type of symbolic basis states
type SState = SBool Var

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

-- | Convenience type for scalars
type Scalar r = Pathsum Nat0 Nat0 r

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
 Convenience (internal) constants)
 ----------------------------}
x0 :: SBool Var
x0 = ofVar $ IVar 0

x1 :: SBool Var
x1 = ofVar $ IVar 1

y0 :: SBool Var
y0 = ofVar $ PVar 0

minusOne :: Exponential r => r
minusOne = ee $ dyadic 1 0

ii :: Exponential r => r
ii = ee $ dyadic 1 1

omega :: Exponential r => r
omega = ee $ dyadic 1 2

halfrt2 :: ScaledDyadicExp
halfrt2 = SDE 1 0

{----------------------------
 Constructors
 ----------------------------}

-- | The identity pathsum
identity :: (Num r, SNatI n) => Pathsum n n r
identity = Pathsum 0 1 (V.map (ofVar . IVar . toInteger) V.universe)

-- | A computational basis state
kket :: Num r => Vec n FF2 -> Ket n r
kket = Pathsum 0 1 . V.map constant

-- | A computational basis state
brak :: (Conditional Var r, Exponential r, TwoRegular r, SNatI n) => Vec n FF2 -> Bra n r
brak vals = Pathsum 1 (divTwo $ ite cond minusOne 1) $ VNil
  where cond = y0*(1 + V.foldl' (*) 1 p)
        p    = V.imap (\i val -> 1 + (constant val) + ofVar (IVar $ toInteger i)) vals

-- | A fresh, 0-valued ancilla
fresh :: Num r => Ket Nat1 r
fresh = Pathsum 0 1 $ V.singleton 0

-- | Initialize a fresh ancilla
initialize :: Num r => FF2 -> Ket Nat1 r
initialize = Pathsum 0 1 . V.singleton . constant

-- | Post select on a particular value (without renormalizing)
postselect :: (Num r, Conditional Var r, Exponential r, TwoRegular r) => FF2 -> Bra Nat1 r
postselect val = Pathsum 1 (divTwo $ ite ((x0 + constant val)*y0) minusOne 1) $ VNil

-- | X gate
xgate :: Num r => Pathsum Nat1 Nat1 r
xgate = Pathsum 0 1 $ V.singleton (1 + x0)

-- | Z gate
zgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat1 Nat1 r
zgate = Pathsum 0 (ite x0 minusOne 1) $ V.singleton x0

-- | Y gate
ygate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat1 Nat1 r
ygate = Pathsum 0 (ii*(ite x0 minusOne 1)) $ V.singleton (1 + x0)

-- | S gate
sgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat1 Nat1 r
sgate = Pathsum 0 (ite x0 ii 1) $ V.singleton x0

-- | T gate
tgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat1 Nat1 r
tgate = Pathsum 0 (ite x0 omega 1) $ V.singleton x0

-- | R_k gate
rkgate :: (Num r, Conditional Var r, Exponential r) => Int -> Pathsum Nat1 Nat1 r
rkgate k = Pathsum 0 (ite x0 (ee $ dyadic 1 k) 1) $ V.singleton x0

-- | H gate
hgate :: Pathsum Nat1 Nat1 ScaledDyadicExp
hgate = Pathsum 1 (halfrt2*(ite (x0*y0) minusOne 1)) $ V.singleton y0

-- | CNOT gate
cxgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat2 Nat2 r
cxgate = Pathsum 0 1 $ x0:::(x0 + x1):::VNil

-- | SWAP gate
swapgate :: (Num r, Conditional Var r, Exponential r) => Pathsum Nat2 Nat2 r
swapgate = Pathsum 0 1 $ x1:::x0:::VNil

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
            ite (ofVar . PVar $ b''-1) ascale (shift sub a'scale)
        s'' = ite (ofVar . PVar $ b''-1) s (shift sub s')

-- | Compose two path sums in parallel
tensor :: (Num r, Shift Var r, SNatI m) =>
  Pathsum m n r -> Pathsum m' n' r -> Pathsum (Plus m m') (Plus n n') r
tensor tmp@(Pathsum b a s) (Pathsum b' a' s') = Pathsum b'' a'' s''
  where sub = shiftAll (inSize tmp) b
        b'' = b+b'
        a'' = a * (shift sub a')
        s'' = (V.++) s (shift sub s')

-- | Functional composition
times :: (Num r, Subst Var r, Shift Var r, SNatI k) =>
  Pathsum m k r -> Pathsum k n r -> Pathsum m n r
times (Pathsum b a s) (Pathsum b' a' s') = Pathsum b'' a'' s''
  where shft = shiftP b
        sub  =
          let f i = Map.insert (IVar $ toInteger i) in
            \v -> Map.findWithDefault (ofVar v) v $ V.ifoldr f Map.empty s
        b''  = b + b'
        a''  = a * subst sub (shift shft a')
        s''  = subst sub (shift shft s')

{-

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
