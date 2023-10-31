{-# LANGUAGE ViewPatterns #-}

{-- Deprecated -}

module Feynman.Verification.SOP where

import Text.Printf

import Data.Bits
import Data.Maybe
import Data.List
import Data.Monoid hiding ((<>))
import Data.Semigroup

import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map

import Feynman.Algebra.Linear hiding (identity)
import Feynman.Algebra.Polynomial
import Feynman.Core hiding (toffoli, subst)
import qualified Feynman.Core as Core
import Feynman.Optimization.PhaseFold (phaseFold)

import Data.Ratio
import Data.Coerce

import Control.Monad
import Data.Function

import Test.QuickCheck
  
import Data.Set (Set)
import qualified Data.Set as Set

{- path sums with polynomials over `a` -}
data SOP a = SOP {
  sde      :: Int,
  inVals   :: Map ID Bool,
  pathVars :: [Int],
  poly     :: Multilinear a,
  outVals  :: Map ID (Multilinear Bool)
  } deriving (Eq)

instance (Show a, Eq a, Num a) => Show (SOP a) where
  show sop = printf "|%s> --> %s%s%s|%s>" is sc sm ph os
    where is = concatMap (\(v, b) -> if b then v else "0") . Map.toList $ inVals sop
          sc = case sde sop of
                 0 -> ""
                 i -> "1/sqrt(2)^" ++ show i ++ " "
          sm = case pathVars sop of
                 [] -> ""
                 xs -> "Sum[" ++ (intercalate "," . map (\i -> pathVar i) $ xs) ++ "] "
          ph = case poly sop == zero of
                 True  -> ""
                 False -> "e^i*pi*" ++ showPoly (poly sop)
          os = concatMap showPoly $ Map.elems $ outVals sop
          showPoly p
            | isMono (simplify p)  = show p
            | otherwise = "(" ++ show p ++ ")"

canonicalizeSOP :: (Num a, Eq a) => SOP a -> SOP a
canonicalizeSOP sop = sop { poly = simplify (poly sop),
                            outVals = Map.map simplify (outVals sop) }

pathVar :: Int -> ID
pathVar i = "p" ++ show i

internalPaths :: SOP a -> [Int]
internalPaths sop = filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop

{- Constructors -}

identity0 :: SOP a
identity0 = SOP 0 Map.empty [] zero Map.empty

identity :: [ID] -> SOP a
identity vars = SOP {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [True | v <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [ofVar v | v <- vars]
  }

identityTrans :: Map ID Bool -> SOP a
identityTrans inp = SOP {
  sde      = 0,
  inVals   = inp,
  pathVars = [],
  poly     = zero,
  outVals  =
      let f v False = zero
          f v True  = ofVar v
      in
        Map.mapWithKey f inp
  }

blank :: [ID] -> SOP a
blank vars = SOP {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [False | i <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [zero | i <- vars]
  }

ofKet :: Map ID Bool -> SOP a
ofKet ket = SOP {
  sde      = 0,
  inVals   = Map.map (\_ -> False) ket,
  pathVars = [],
  poly     = zero,
  outVals  = Map.map constant ket
  }


{- Operators -}
compose :: (Eq a, Num a) => SOP a -> SOP a -> SOP a
compose u v
  | u == mempty = v
  | v == mempty = u
  | otherwise   =
    let varShift = case null (pathVars v) of
          True  -> 0
          False -> maximum ([-1] ++ pathVars u) - minimum (pathVars v) + 1
        sub =
          let f v True  = Map.insert v $ Map.findWithDefault (ofVar v) v (outVals u)
              f v False = error $ "Composing " ++ v ++ " with |0> on the right"
              initMap = Map.fromList [(pathVar i, ofVar $ pathVar $ i + varShift) | i <- pathVars v]
          in
            Map.foldrWithKey f initMap (inVals v)
    in SOP {
      sde      = sde u + sde v,
      inVals   = Map.union (inVals u) (inVals v),
      pathVars = pathVars u ++ map (+ varShift) (pathVars v),
      poly     = poly u + substMany sub (poly v),
      outVals  = Map.union (Map.map (simplify . substMany sub) $ outVals v) (outVals u)
      }

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

{- Verification -}

type CounterEx = String -- Temporary

data VerificationResult a =
    Identity [Rule]
  | NotIdentity CounterEx
  | Unknown (SOP a)

-- Verifies directly against a path sum
verifySpec :: SOP Z8 -> [ID] -> [ID] -> [Primitive] -> VerificationResult Z8
verifySpec spec vars inputs gates =
  let sop        = circuitSOPWithHints vars (dagger gates)
      (pf, sop') = reduce $ (spec <> sop)
  in
    case sop' == identityTrans (inVals spec) of
      True  -> Identity pf
      False -> Unknown sop'

verifyPermutation :: SOP Z8 -> [Primitive] -> VerificationResult Z8
verifyPermutation spec gates =
  let sop         = circuitSOP (dagger gates)
      bra         = Map.mapWithKey (\v b -> if b then ofVar v else zero) $ inVals spec
      (pf, sop')  = reduce $ restrictGeneral (spec <> sop) bra
      checkIt sop = pathVars sop == [] && sde sop == 0
  in
    case (checkIt sop', axiomKill sop') of
      (True, _)       -> Identity pf
      (False, Just i) -> NotIdentity $ "No valid substitution for " ++ pathVar i ++ " (" ++ show sop' ++ ")"
      (False, _)      -> Unknown sop'

validateIsometry :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> VerificationResult Z8
validateIsometry global vars inputs c1 c2 =
  let sop     = circuitSOPWithHints vars (c1 ++ dagger c2)
      ket     = blank (vars \\ inputs)
      bra     = Map.mapWithKey (\v b -> if b then ofVar v else zero) $ inVals (ket <> sop)
      (pf, sop') =
        let (pf, sop') = reduce $ restrictGeneral (ket <> sop) bra in
          if global
          then (pf, sop' { poly = dropConstant $ poly sop' })
          else (pf, sop')
      checkIt sop = canonicalizeSOP sop == canonicalizeSOP (identityTrans $ inVals sop)
  in
    case (checkIt sop', axiomKill sop') of
      (True, _)       -> Identity pf
      (False, Just i) -> NotIdentity $ "No valid substitution for " ++ pathVar i ++ " (" ++ show sop' ++ ")"
      (False, _)      -> Unknown sop'

validateToScale :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> VerificationResult Z8
validateToScale global vars inputs c1 c2 =
  let sop     = circuitSOPWithHints vars (c1 ++ dagger c2)
      ket     = blank (vars \\ inputs)
      bra     = Map.mapWithKey (\v b -> if b then ofVar v else zero) $ inVals (ket <> sop)
      (pf, sop') =
        let (pf, sop') = reduce $ restrictGeneral (ket <> sop) bra in
          if global
          then (pf, sop' { poly = dropConstant $ poly sop' })
          else (pf, sop')
      checkIt sop =
        let out = outVals sop in
          all (\v -> not (v `appearsIn` (poly sop)) && out!v == ofVar v) inputs
  in
    case (checkIt sop', axiomKill sop') of
      (True, _)       -> Identity pf
      (False, Just i) -> NotIdentity $ "No valid substitution for " ++ pathVar i ++ " (" ++ show sop' ++ ")"
      (False, _)      -> Unknown sop'

validateOnInputs :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> VerificationResult Z8
validateOnInputs global vars inputs c1 c2 =
  let sop     = circuitSOPWithHints vars (c1 ++ dagger c2)
      ket     = blank (vars \\ inputs)
      (pf, sop') =
        let (pf, sop') = reduce $ ket <> sop in
          if global
          then (pf, sop' { poly = dropConstant $ poly sop' })
          else (pf, sop')
      checkIt sop =
        let out = outVals sop in
          all (\v -> not (v `appearsIn` (poly sop)) && out!v == ofVar v) inputs
  in
    if checkIt sop'
    then Identity pf
    else Unknown sop'

{- Tests & experiments -}

tof = [ H "z",
        T "x", T "y", T "z", 
        CNOT "x" "y", CNOT "y" "z", CNOT "z" "x",
        Tinv "x", Tinv "y", T "z",
        CNOT "y" "x",
        Tinv "x",
        CNOT "y" "z", CNOT "z" "x", CNOT "x" "y",
        H "z" ]

cH = [ Sinv "y", H "y", Tinv "y", CNOT "x" "y", T "y", H "y", S "y"]

omeg = [ S "x", H "x", S "x", H "x", S "x", H "x" ]

cT = [H "z", Sinv "x", CNOT "x" "y", CNOT "y" "z", CNOT "z" "x", T "x", Tinv "z",
      CNOT "y" "x", CNOT "y" "z", T "x", Tinv "z", CNOT "x" "z", H "x", T "x", H "x",
      CNOT "x" "z", Tinv "x", T "z", CNOT "y" "z", CNOT "y" "x", Tinv "x", T "z",
      CNOT "z" "x", CNOT "y" "z", CNOT "x" "y", S "x", H "z"]

cTSpec x y z = SOP {
  sde      = 0,
  inVals   = Map.fromList [(x, True), (y, True), (z, False)],
  pathVars = [],
  poly     = ofTerm (Z8 1) [x, y],
  outVals  = Map.fromList [(x, ofVar x), (y, ofVar y), (z, zero)]
  }

cHSpec x y = SOP {
  sde      = 1,
  inVals   = Map.fromList [(x, True), (y, True)],
  pathVars = [0],
  poly     = ofTerm (Z8 4) [x, y, pathVar 0],
  outVals  = Map.fromList [(x, ofVar x), (y, ofVar y + ofTerm True [x, y] + ofTerm True [x, pathVar 0])]
  }


-- toffoli gates
toffoli :: ID -> ID -> ID -> [Primitive]
toffoli x y z =
  [ H z,
    T x, T y, T z, 
    CNOT x y, CNOT y z, CNOT z x,
    Tinv x, Tinv y, T z,
    CNOT y x,
    Tinv x,
    CNOT y z, CNOT z x, CNOT x y,
    H z ]

toffoliN :: [ID] -> [Primitive]
toffoliN = go 0
  where go i []         = []
        go i (x:[])     = []
        go i (x:y:[])   = [ CNOT x y ]
        go i (x:y:z:[]) = toffoli x y z
        go i (x:y:xs)   =
          let anc        = "_anc" ++ show i
              subproduct = toffoli x y anc
          in
            subproduct ++ go (i+1) (anc:xs) ++ dagger subproduct

barencoTof :: [ID] -> ID -> [ID] -> [Primitive]
barencoTof [] t _          = []
barencoTof (c:[]) t _      = [CNOT c t]
barencoTof (c:c':[]) t _   = toffoli c c' t
barencoTof (c:cs) t (d:ds) = go (c:cs) t (d:ds) ++ go cs d ds
  where go (c:c':[]) t _   = toffoli c c' t
        go (c:cs) t (d:ds) = toffoli c d t ++ go cs d ds ++ toffoli c d t

barencoOne :: [ID] -> ID -> ID -> [Primitive]
barencoOne [] t anc        = []
barencoOne (c:[]) t anc    = [CNOT c t]
barencoOne (c:c':[]) t anc = toffoli c c' t
barencoOne cs t anc        = circ ++ circ where
  circ       = barencoTof cs'' anc cs' ++ barencoTof (cs' ++ [anc]) t cs''
  (cs',cs'') = splitAt (length cs `div` 2) cs

nielsenOne :: [ID] -> ID -> ID -> [Primitive]
nielsenOne [] t anc        = []
nielsenOne (c:[]) t anc    = [CNOT c t]
nielsenOne (c:c':[]) t anc = toffoli c c' t
nielsenOne cs t anc        = circ ++ barencoTof (cs' ++ [anc]) t cs'' ++ circ where
  circ       = barencoTof cs'' anc cs'
  (cs',cs'') = splitAt (length cs `div` 2) cs

toffoliNSpec :: [ID] -> SOP Z8
toffoliNSpec xs = SOP {
  sde      = 0,
  inVals   = Map.fromList $ [(x, True) | x <- xs] ++ [(y, False) | y <- anc],
  pathVars = [],
  poly     = zero,
  outVals  = Map.insert (last xs) product outInit
  }
  where anc     = ["_anc" ++ show i | i <- [0..length xs - 4]]
        product = ofVar (last xs) + ofTerm True (init xs)
        outInit = Map.fromList $ [(x, ofVar x) | x <- xs] ++ [(y, zero) | y <- anc]

verifyToffoliN n () = do
  putStrLn $ "Verifying Toffoli, N=" ++ show n
  printVerStats (toffoliN inputs)
  case verifySpec (toffoliNSpec inputs) vars inputs (toffoliN inputs) of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ map (\i -> [i]) ['a'..]
        vars   = inputs ++ ["_anc" ++ show i | i <- [0..n-4]]

-- General product gates
rToffoli x y z = [H z, Tinv z, CNOT y z, T z, CNOT x z, Tinv z, CNOT y z, T z, CNOT x z, H z]

rToffoli4 w x y z =
  let conj = [H z, T z, CNOT y z, Tinv z, H z] in
    conj ++ [CNOT w z, T z, CNOT x z, Tinv z, CNOT w z, T z, CNOT x z, Tinv z] ++ conj

maslovToffoli :: [ID] -> [Primitive]
maslovToffoli = go 0
  where go i []         = []
        go i (w:[])     = []
        go i (w:z:[])   = [CNOT w z]
        go i (w:x:z:[]) = toffoli w x z
        go i (w:x:y:xs) =
          let anc = "_anc" ++ show i
              sub = rToffoli4 w x y anc
          in
            sub ++ go (i+1) (anc:xs) ++ (dagger sub)

verifyMaslovN n () = do
  putStrLn $ "Verifying Maslov, N=" ++ show n
  printVerStats (maslovToffoli inputs)
  case verifySpec (toffoliNSpec inputs) vars inputs (maslovToffoli inputs) of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ map (\i -> [i]) ['a'..]
        vars   = inputs ++ ["_anc" ++ show i | i <- [0..n-4]]

{- Adders -}

carryRipple n a b c =
  let anc          = ["_anc" ++ show i | i <- [0..n-1]]
      carry        = ["_carry" ++ show i | i <- [0..n-1]]
      maj a b c c' = [CNOT b c] ++ toffoli a c c' ++ [CNOT b c] ++ toffoli b c c'
      plus a b c d = [CNOT a d, CNOT b d, CNOT c d]
      compute      = [CNOT (a!!0) (anc!!0), CNOT (b!!0) (anc!!0)] ++
                     concatMap (\i -> maj (a!!i) (b!!i) (carry!!i) (carry!!(i+1)) ++
                                      plus (a!!(i+1)) (b!!(i+1)) (carry!!(i+1)) (anc!!(i+1))) [0..n-2]
      copy         = map (\i -> CNOT (anc!!i) (c!!i)) [0..n-1]
  in
    compute ++ copy ++ (dagger compute)

adderOOPSpec :: Int -> [ID] -> [ID] -> [ID] -> SOP Z8
adderOOPSpec n a b c = SOP {
  sde      = 0,
  inVals   = Map.fromList $ [(v, True) | v <- a ++ b ++ c] ++ [(v, False) | v <- anc ++ carry],
  pathVars = [],
  poly     = zero,
  outVals  = snd $ foldl' f (zero, constOuts) [0..n-1]
  }
  where anc          = ["_anc" ++ show i | i <- [0..n-1]]
        carry        = ["_carry" ++ show i | i <- [0..n-1]]
        constOuts    = Map.fromList $ [(v, ofVar v) | v <- a ++ b] ++ [(v, zero) | v <- anc ++ carry]
        f (carry, map) i =
          let ai = ofVar $ (a!!i)
              bi = ofVar $ (b!!i)
              ci = ofVar $ (c!!i)
          in
            (ai*carry + bi*carry + ai*bi, Map.insert (c!!i) (ci + carry + ai + bi) map)
  
verifyOOPAdder n () = do
  putStrLn $ "Verifying Adder, N=" ++ show n
  printVerStats (carryRipple n a b c)
  case verifySpec (adderOOPSpec n a b c) (a ++ b ++ c ++ anc ++ carry) (a ++ b ++ c) (carryRipple n a b c) of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where a = ["a" ++ show i | i <- [0..n-1]]
        b = ["b" ++ show i | i <- [0..n-1]]
        c = ["c" ++ show i | i <- [0..n-1]]
        anc   = ["_anc" ++ show i | i <- [0..n-1]]
        carry = ["_carry" ++ show i | i <- [0..n-1]]

{- Hidden shift algorithm -}

genCCZ :: [String] -> Gen [Primitive]
genCCZ xs = do
  x <- elements xs
  y <- elements $ xs \\ [x]
  z <- elements $ xs \\ [x,y]
  return $ [Uninterp "CCZ" [x, y, z]]

genCZ :: [String] -> Gen [Primitive]
genCZ xs = do
  x <- elements xs
  y <- elements $ xs \\ [x]
  return $ [CZ x y]

genZ :: [String] -> Gen [Primitive]
genZ xs = do
  x <- elements xs
  return $ [Z x]

genMaioranaG :: [String] -> Int -> Gen [Primitive]
genMaioranaG xs 0 = return []
genMaioranaG xs i = do
  ccz   <- genCCZ xs
  cliff <- replicateM 200 $ oneof [genCZ xs, genZ xs]
  next  <- genMaioranaG xs (i-1)
  return $ concat (ccz:cliff) ++ next

hiddenShift :: Int -> Int -> Gen ([Primitive], [String])
hiddenShift n alternations = do
  s <- sublistOf vars
  g <- genMaioranaG (take n2 vars) alternations
  let hTrans = map H vars
      xTrans = map X s 
      cTrans = concat [CZ (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      f' = (Core.subst (\i -> Map.findWithDefault i i sub) g) ++ cTrans
      f  = xTrans ++ g ++ cTrans ++ xTrans
  return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

hiddenShiftQuantum :: Int -> Int -> Gen [Primitive]
hiddenShiftQuantum n alternations = do
  g <- genMaioranaG (take n2 vars) alternations
  let hTrans = map H vars
      xTrans = [CNOT ("y" ++ show i) ("x" ++ show i) | i <- [0..n-1]]
      cTrans = concat [cz (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      f' = (Core.subst (\i -> Map.findWithDefault i i sub) g) ++ cTrans
      f  = xTrans ++ g ++ cTrans ++ xTrans
  return $ hTrans ++ f ++ hTrans ++ f' ++ hTrans
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

hiddenShiftSpec :: Int -> [String] -> SOP Z8
hiddenShiftSpec n string = SOP {
  sde      = 0,
  inVals   = Map.fromList [("x" ++ show i, False) | i <- [0..n-1]],
  pathVars = [],
  poly     = zero,
  outVals  =
     let f v = (v, if v `elem` string then one else zero) in
       Map.fromList $ map f ["x" ++ show i | i <- [0..n-1]]
  }

hiddenShiftQuantumSpec :: Int -> SOP Z8
hiddenShiftQuantumSpec n = SOP {
  sde      = 0,
  inVals   = Map.fromList $ [("x" ++ show i, False) | i <- [0..n-1]] ++
                            [("y" ++ show i, True)  | i <- [0..n-1]],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ [("x" ++ show i, ofVar ("y" ++ show i)) | i <- [0..n-1]] ++
                            [("y" ++ show i, ofVar ("y" ++ show i)) | i <- [0..n-1]]
  }

verifyHiddenShift n a () = do
  putStrLn $ "Verifying random Hidden Shift, n=" ++ show n ++ ", A=" ++ show a
  (circ, string) <- generate $ hiddenShift n a
  printVerStats (circ)
  case verifySpec (hiddenShiftSpec n string) vars [] circ of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where vars   = ["x" ++ show i | i <- [0..n-1]]

verifyHiddenShiftQuantum n a () = do
  putStrLn $ "Verifying random Symbolic Shift, n=" ++ show n ++ ", A=" ++ show a
  circ <- generate $ hiddenShiftQuantum n a
  printVerStats (circ)
  case verifySpec (hiddenShiftQuantumSpec n) vars inputs circ of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where vars   = ["x" ++ show i | i <- [0..n-1]] ++ inputs
        inputs = ["y" ++ show i | i <- [0..n-1]]

simulateHiddenShift n a () = do
  (circ, string) <- generate $ hiddenShift n a
  putStrLn $ "Simulating random Hidden Shift, n=" ++ show n
    ++ ", A=" ++ show a
    ++ ", x=" ++ show (fromBits . map (`elem` string) . reverse . sort $ vars)
  printVerStats (circ)
  let sop = circuitSOPWithHints vars circ
  print $ reduce (blank vars <> sop)
  where vars = ["x" ++ show i | i <- [0..n-1]]
  

{- Circuit designs -}

minimalProductGate []     t = []
minimalProductGate (c:[]) t = [CNOT c t]
minimalProductGate (c:cs) t = tmp ++ minimalProductGate cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate1 []         t = []
minimalProductGate1 (c:[])     t = [CNOT c t]
minimalProductGate1 (c1:c2:[]) t =
  [H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t, CNOT t c1,
   T c1, Tinv t, CNOT t c1, CNOT c2 t, H t]
minimalProductGate1 (c:cs)     t = tmp ++ minimalProductGate1 cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate2 []         t = []
minimalProductGate2 (c:[])     t = [CNOT c t]
minimalProductGate2 (c1:c2:[]) t =
  [Sinv t, H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t,
   CNOT t c1, T c1, Tinv t, CNOT t c1, CNOT c2 t, H t, S t]
minimalProductGate2 (c:cs)     t = tmp ++ minimalProductGate2 cs t ++ dagger tmp
  where tmp = [Sinv t, H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate3 []         t = []
minimalProductGate3 (c:[])     t = [CNOT c t]
minimalProductGate3 (c1:c2:[]) t =
  [H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t, CNOT t c1, T c1, Tinv t, CNOT t c1, CNOT c2 t, H t]
minimalProductGate3 (c:cs)     t = tmp ++ minimalProductGate3 cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate4 []     t = []
minimalProductGate4 (c:[]) t = [CNOT c t]
minimalProductGate4 (c:cs) t = tmp ++ minimalProductGate4 cs t ++ dagger tmp
  where tmp = [S t, H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate5 []     t = []
minimalProductGate5 (c:[]) t = [CNOT c t]
minimalProductGate5 (c:cs) t = tmp ++ minimalProductGate5 cs t ++ dagger tmp
  where tmp = [S t, H t, CNOT t c, Tinv c, CNOT t c] 

generalProductGate []     t = []
generalProductGate (c:[]) t = [CNOT c t]
generalProductGate (c:cs) t =
  [H t] ++ tmp ++ generalProductGate cs t ++ dagger tmp ++ dagger (generalProductGate cs t) ++ [H t]
  where tmp = [CNOT t c, T t, Tinv c, CNOT t c] 

generalProductGateN n []     t = []
generalProductGateN n (c:[]) t = [CNOT c t]
generalProductGateN n (c:cs) t
  | n == 0    = generalProductGate (c:cs) t
  | otherwise = tmp ++ generalProductGateN (n-1) cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

rToffoli4Corrected w x y z =
  let conj = [H z, T z, CNOT y z, Tinv z, H z]
      corr = [T z, CNOT w z, Tinv z, CNOT x z, T z, CNOT w z, Tinv z, CNOT x z]
  in
    corr ++ conj ++ [CNOT w z, T z, CNOT x z, Tinv z, CNOT w z, T z, CNOT x z, Tinv z] ++ conj

rToffoli5 v w x y z =
  let conj = [H z, T z, CNOT y z, Tinv z] in
    conj ++ rToffoli4Corrected v w x z ++ dagger conj

rToffoli5' v w x y z anc =
  [H z] ++ toffoli z y anc ++ [H anc] ++ rToffoli4 v w x anc ++ [H anc] ++ toffoli z y anc ++ [H z]

fun0888 a b c d e anc = temp ++ [CNOT anc e] ++ dagger temp ++ [CNOT anc e]
  where temp = minimalProductGate1 [d, c, b, a] anc

fun7880 a b c d e anc = temp ++ [CNOT anc e] ++ dagger temp ++ [CNOT anc e] ++ (toffoli c d e)
  where temp = minimalProductGate2 [d, c, b, a] anc

fun00808080 a b c d e f anc = temp ++ [CNOT anc f] ++ dagger temp ++ [CNOT anc f]
  where temp = generalProductGateN 2 [e, d, c, b, a] anc

fun88a22a2a a b c d e f anc = temp ++ [CNOT anc f] ++ dagger temp ++ [CNOT anc f]
  where temp = minimalProductGate [e, d, c, b, a] anc

fun88088080 a b c d e f anc = temp ++ [CNOT anc f] ++ dagger temp ++ [CNOT anc f]
  where temp = minimalProductGate1 [e, d, c, b, a] anc

class8880 = fun0888

classe880 = fun7880

class80808000 = fun00808080
fun0a000010   = class80808000

classa8808000 = fun88a22a2a
fun80088820   = classa8808000

class88808080 = fun88088080

countT = foldr (+) 0 . map f where
  f (T _)    = 1
  f (Tinv _) = 1
  f _        = 0

-- Recurrences for constructions

-- T-count of the barenco toffoli
barencoT :: Int -> Int
barencoT 0 = 0
barencoT 1 = 0
barencoT 2 = 7
barencoT n = 16 + 12*(n-3)

crTGS :: Int -> Int
crTGS 0 = 0
crTGS 1 = 0
crTGS n = 4 + case n `mod` 2 of
  0 -> 4*(barencoT $ n `div` 2)
  1 -> 2*(barencoT $ n `div` 2) + 2*(barencoT $ 1 + (n `div` 2))

crTi :: Int -> Int
crTi 0 = 0
crTi 1 = 0
crTi n = 4 + case n `mod` 2 of
  0 -> 4*(crTi $ n `div` 2)
  1 -> 2*(crTi $ n `div` 2) + 2*(crTi $ 1 + (n `div` 2))

-- T-count of the balanced construction
cr1TMemo :: (Int -> (Int,Int)) -> Int -> (Int, Int)
cr1TMemo memo 0 = (0,0)
cr1TMemo memo 1 = (1,0)
cr1TMemo memo n = (k,4+2*(snd $ memo k)+2*(snd $ memo (n-k))) where
  k = n `div` 2

-- T-count of the unbalanced construction
cr2TMemo :: (Int -> (Int,Int)) -> Int -> (Int, Int)
cr2TMemo memo 0 = (0,0)
cr2TMemo memo 1 = (1,0)
cr2TMemo memo n = (k,4+t) where
  (k,t) = minimumBy (\(_,t1) (_,t2) -> compare t1 t2) $ map f $ reverse [1..n-1]
  f k   = (k, (snd $ cr1TMemo memo k) + 2*(snd $ memo (n-k)))

memoize :: (Int -> a) -> Int -> a
memoize f = (map f [0..] !!)

cr2T :: Int -> (Int,Int)
cr2T = fix (memoize . cr2TMemo)

cr1T :: Int -> (Int,Int)
cr1T = cr1TMemo cr2T

bestSplit :: Int -> Int
bestSplit = fst . cr2T

-- Circuit constructions
controllediXGS []     t = []
controllediXGS (c:[]) t = [CNOT c t]
controllediXGS cs     t = [H t, Tinv t] ++
                          barencoTof cs' t cs'' ++
                          [T t] ++
                          barencoTof cs'' t cs' ++
                          [Tinv t] ++
                          barencoTof cs' t cs'' ++
                          [T t] ++
                          barencoTof cs'' t cs' ++
                          [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controllediX []     t = []
controllediX (c:[]) t = [CNOT c t]
controllediX cs     t = [H t, Tinv t] ++
                          controllediX' cs' t ++
                          [T t] ++
                          controllediX' cs'' t ++
                          [Tinv t] ++
                          dagger (controllediX' cs' t) ++
                          [T t] ++
                          dagger (controllediX' cs'' t) ++
                          [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controllediX' []     t = []
controllediX' (c:[]) t = [CNOT c t]
controllediX' cs     t = [H t, Tinv t] ++
                        controlledXBullet cs'' t ++
                        [T t] ++
                        controlledXBullet cs' t ++
                        [Tinv t] ++
                        dagger (controlledXBullet cs'' t) ++
                        [T t] ++
                        dagger (controlledXBullet cs' t) ++
                        [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledZX' cs t = [S t] ++ controllediX' cs t ++ [Sinv t]

controlledXBullet []     t = []
controlledXBullet (c:[]) t = [CNOT c t]
controlledXBullet cs     t = [H t, Tinv t] ++
                             controlledXStar cs'' t ++
                             [T t] ++
                             controlledXStar cs' t ++
                             [Tinv t] ++
                             dagger (controlledXStar cs'' t) ++
                             [T t] ++
                             dagger (controlledXStar cs' t) ++
                             [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXStar []     t = []
controlledXStar (c:[]) t = [CNOT c t]
controlledXStar cs     t = [H t, T t] ++
                           controlledXStar cs'' t ++
                           [Tinv t] ++
                           controlledXBullet cs' t ++
                           [T t] ++
                           dagger (controlledXStar cs'' t) ++
                           [Tinv t] ++
                           [H t]
  where (cs', cs'') = splitAt (bestSplit $ length cs) cs

controllediXClean []         t anc = []
controllediXClean (c:[])     t anc = [CNOT c t]
controllediXClean (c1:c2:[]) t anc = toffoli c1 c2 t
controllediXClean cs         t anc = controlledXStar cs'' anc ++
                                     [H t, T t] ++
                                     controlledXBullet cs' t ++
                                     [Tinv t, CNOT anc t, T t] ++
                                     dagger (controlledXBullet cs' t) ++
                                     [Tinv t, CNOT anc t, H t] ++
                                     dagger (controlledXStar cs'' anc)
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXClean []         t anc = []
controlledXClean (c:[])     t anc = [CNOT c t]
controlledXClean (c1:c2:[]) t anc = toffoli c1 c2 t
controlledXClean cs         t anc = controlledXStar cs anc ++
                                    [CNOT anc t] ++
                                    dagger (controlledXStar cs anc)

controlledXDirty []         t anc = []
controlledXDirty (c:[])     t anc = [CNOT c t]
controlledXDirty (c1:c2:[]) t anc = toffoli c1 c2 t
controlledXDirty cs         t anc = controlledXStar cs anc ++
                                    [CNOT anc t] ++
                                    dagger (controlledXStar cs anc) ++
                                    [CNOT anc t]

partialPhase :: [ID] -> [ID] -> [Primitive]
partialPhase []         _    = []
partialPhase (a:[])     _    = [Z a]
partialPhase (a:b:[])   _    = [S a, CNOT b a, Sinv a, CNOT b a]
partialPhase (a:b:c:[]) _    = [T a, CNOT b a, Tinv a, CNOT c a, T a, CNOT b a, Tinv a, CNOT c a]
partialPhase (x:y:xs) (z:ys) = partialTof ++ partialPhase (z:xs) ys ++ dagger (partialTof) where
  partialTof = [H z] ++ partialPhase [z,x,y] [] ++ [H z]

barencoRTof :: [ID] -> ID -> [ID] -> [Primitive]
barencoRTof xs y ys = [H y] ++ partialPhase (y:xs) ys ++ [H y]

barencoRTofBullet :: [ID] -> ID -> [ID] -> [Primitive]
barencoRTofBullet (x:xs) y ys
  | xs == []  = [H y] ++ partialPhase (y:x:xs) ys ++ [H y]
  | otherwise =  [H y, Tinv y, CNOT x y, T y] ++ barencoRTof xs y ys ++ [Tinv y, CNOT x y, T y, H y]

barencoThrees :: [ID] -> ID -> [ID] -> [Primitive]
barencoThrees xs t ys = [H t] ++ go xs t ys ++ [H t] where
  go [] t _            = [Z t]
  go (x:[]) t _        = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t _      = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t (z:ys)
    | length xs >= 2 = rToffoli4 x y t z ++ go xs z ys ++ (dagger $ rToffoli4 x y t z)
    | otherwise      = rToffoli x t z ++ go (y:xs) z ys ++ (dagger $ rToffoli x t z)


controllediXLinear []     t = []
controllediXLinear (c:[]) t = [CNOT c t]
controllediXLinear cs     t = [H t, Tinv t] ++
                          barencoRTof cs' t cs'' ++
                          [T t] ++
                          barencoRTof cs'' t cs' ++
                          [Tinv t] ++
                          dagger (barencoRTof cs' t cs'') ++
                          [T t] ++
                          dagger (barencoRTof cs'' t cs') ++
                          [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXBulletLinear []     t = []
controlledXBulletLinear (c:[]) t = [CNOT c t]
controlledXBulletLinear cs     t = [H t, Tinv t] ++
                          barencoRTofBullet cs' t cs'' ++
                          [T t] ++
                          barencoRTofBullet cs'' t cs' ++
                          [Tinv t] ++
                          dagger (barencoRTofBullet cs' t cs'') ++
                          [T t] ++
                          dagger (barencoRTofBullet cs'' t cs') ++
                          [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXStarLinear []     t = []
controlledXStarLinear (c:[]) t = [CNOT c t]
controlledXStarLinear cs     t = [H t, T t] ++
                                  barencoRTofBullet cs'' t cs' ++
                                  [Tinv t] ++
                                  barencoRTof cs' t cs'' ++
                                  [T t] ++
                                  dagger (barencoRTofBullet cs'' t cs') ++
                                  [Tinv t, H t]
  where (cs', cs'') = splitAt ((length cs + 2) `div` 2) cs

controlledXStarStar []     t = []
controlledXStarStar (c:[]) t = [CNOT c t]
controlledXStarStar (c:cs) t = [H t, T t] ++
                               [CNOT c t] ++
                               [Tinv t] ++
                               controllediXLinear cs t ++
                               [T t] ++
                               [CNOT c t] ++
                               [Tinv t, H t]

controlledXStarUlt []     t = []
controlledXStarUlt (c:[]) t = [CNOT c t]
controlledXStarUlt cs     t = [H t, T t] ++
                              barencoRTofBullet cs'' t cs' ++
                              [Tinv t] ++
                              barencoThrees cs' t cs'' ++
                              [T t] ++
                              dagger (barencoRTofBullet cs'' t cs') ++
                              [Tinv t, H t]
  where (cs', cs'') = splitAt (bestSplit $ length cs) cs
        bestSplit k = fromMaybe k . find (f k) . reverse $ [0..k]
        f k i       = floor (fromIntegral i / 2.0) <= (k-i)

costC1 :: Int -> Int
costC1 0 = 0
costC1 1 = 0
costC1 2 = 4
costC1 3 = 12
costC1 4 = 20
costC1 5 = 28
costC1 6 = 36
costC1 k = 52 + 16*(k-7)

costC2 :: Int -> Int
costC2 0 = 0
costC2 1 = 0
costC2 2 = 4
costC2 3 = 8
costC2 4 = 16
costC2 5 = 24
costC2 6 = 32
costC2 7 = 40
costC2 8 = 48
costC2 k
  | k `mod` 2 == 0 = costC2 (k-1) + 8
  | otherwise      = costC2 (k-1) + 16

costC3 :: Int -> Int
costC3 0 = 0
costC3 1 = 0
costC3 2 = 4
costC3 3 = 8
costC3 4 = 16
costC3 5 = 24
costC3 6 = 32
costC3 7 = 40
costC3 8 = 48
costC3 9 = 56
costC3 10 = 64
costC3 k
  | (k-11) `mod` 3 == 0 = costC3 (k-1) + 16
  | otherwise           = costC3 (k-1) + 8

toffoliPermSpec :: [ID] -> ID -> SOP Z8
toffoliPermSpec xs y = SOP {
  sde      = 0,
  inVals   = i,
  pathVars = [],
  poly     = zero,
  outVals  = o
  }
  where i = Map.fromList $ [(x, True) | x <- y:xs]
        o = Map.fromList $ [(x, ofVar x) | x <- xs] ++ [(y, ofVar y + ofTerm True xs)]

verifyC1 n () = do
  putStrLn $ "Verifying relative phase Toffoli, N=" ++ show n
  printVerStats (controlledXBulletLinear inputs "y")
  case verifyPermutation (toffoliPermSpec inputs "y") (controlledXBulletLinear inputs "y") of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ ["x" ++ show i | i <- [0..]]

verifyC2 n () = do
  putStrLn $ "Verifying relative phase Toffoli, N=" ++ show n
  printVerStats (controlledXStarLinear inputs "y")
  case verifyPermutation (toffoliPermSpec inputs "y") (controlledXStarLinear inputs "y") of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ ["x" ++ show i | i <- [0..]]

verifyC3 n () = do
  putStrLn $ "Verifying relative phase Toffoli, N=" ++ show n
  printVerStats (controlledXStarUlt inputs "y")
  case verifyPermutation (toffoliPermSpec inputs "y") (controlledXStarUlt inputs "y") of
    Identity _ -> putStrLn $ "  Success!"
    _          -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ ["x" ++ show i | i <- [0..]]

testGate a b c d = dagger g ++ [CNOT c d] ++ dagger g ++ toffoli a b d ++ g ++ [CNOT c d] ++ g where
  g = [S d, H d, T d, H d, Sinv d]

-- T-count of the unbalanced construction

{- Clifford identities -}

-- Defined gates
omega x = [T x, X x, T x, X x]

c1 x = concat $ replicate 8 (omega x)
  
c2 x = [H x, H x]
c3 x = [S x, S x, S x, S x]
c4 x = [S x, H x, S x, H x, S x, H x] ++ dagger (omega x)

c5  x y = cz x y ++ cz x y
c6  x y = [S x] ++ cz x y ++ [Sinv x] ++ cz x y
c7  x y = [S y] ++ cz x y ++ [Sinv y] ++ cz x y
c8  x y = [H x, S x, S x, H x] ++ cz x y ++ [H x, Sinv x, Sinv x, Sinv y, H x, Sinv y] ++ cz x y
c9  x y = [H y, S y, S y, H y] ++ cz x y ++ [H y, Sinv y, Sinv y, Sinv x, H y, Sinv x] ++ cz x y
c10 x y = cz x y ++ [H x] ++ cz x y ++ omega x ++ [Sinv x, H x, Sinv x, Sinv y] ++ cz x y ++ [H x, Sinv x]
c11 x y = cz x y ++ [H y] ++ cz x y ++ omega x ++ [Sinv y, H y, Sinv y, Sinv x] ++ cz x y ++ [H y, Sinv y]

c12 x y z = cz y z ++ cz x y ++ cz y z ++ cz x y
c13 x y z =
  cz x y ++ [H x, H y] ++ cz x y ++ [H y, H z] ++ cz y z ++ [H y, H z] ++ cz x y ++ [H x, H y] ++ cz x y ++
  cz y z ++ [H y, H z] ++ cz y z ++ [H x, H y] ++ cz x y ++ [H x, H y] ++ cz y z ++ [H y, H z] ++ cz y z
c14 x y z =
  cz x y ++ [H x, H y] ++ cz x y ++ [H x, H y] ++ cz y z ++
  cz x y ++ [H x, H y] ++ cz x y ++ [H x, H y] ++ cz y z ++
  cz x y ++ [H x, H y] ++ cz x y ++ [H x, H y] ++ cz y z
c15 x y z =
  cz y z ++ [H y, H z] ++ cz y z ++ [H y, H z] ++ cz x y ++
  cz y z ++ [H y, H z] ++ cz y z ++ [H y, H z] ++ cz x y ++
  cz y z ++ [H y, H z] ++ cz y z ++ [H y, H z] ++ cz x y

verifyClifford () = sequence_ . map f $ onequbit ++ twoqubit ++ threequbit
  where onequbit   = mapSnds ($ "x") [("c1", c1), ("c2", c2), ("c3", c3), ("c4", c4)]
        twoqubit   = mapSnds ($ "y") . mapSnds ($ "x") $ [("c5", c5), ("c6", c6), ("c7", c7), ("c8", c8),
                                                          ("c9", c9), ("c10", c10), ("c11", c11)]
        threequbit = mapSnds ($ "z") . mapSnds ($ "y") . mapSnds ($ "x") $ [("c12", c12), ("c13", c13),
                                                                            ("c14", c14), ("c15", c15)]
        f (name, c) = case validateIsometry False ["x", "y", "z"] ["x", "y", "z"] c [] of
          Identity _ -> putStrLn $ "Successfully verified relation " ++ name
          _          -> putStrLn $ "ERROR: Failed to verify relation " ++ name
        mapSnds f xs    = map (mapSnd f) xs
        mapSnd f (a, b) = (a, f b)

{- Clifford+T identities -}

-- Defined gates
tx x = [H x, T x, H x]
ty x = [S x] ++ tx x ++ [Sinv x]

t1 x = concat $ replicate 8 (omega x)

t2 x = [H x, H x]
t3 x = concat $ replicate 8 [T x]
t4 x = [H x] ++ tx x ++ [H x, Tinv x]
t5 x = [H x] ++ ty x ++ [Z x] ++ (dagger $ ty x)
t6 x = [H x, T x, H x] ++ (dagger $ tx x)
t7 x = [S x] ++ tx x ++ [Sinv x] ++ (dagger $ ty x)
t8 x = [S x] ++ ty x ++ [Z x, H x, Sinv x] ++ (dagger $ tx x)
t9 x = [S x, T x, Sinv x, Tinv x]

t10 x y = [T x] ++ cz x y ++ [Tinv x] ++ cz x y
t11 x y = [CNOT x y, CNOT y x, T x, CNOT y x, CNOT x y, Tinv y]
t12 x y = c ++ c
  where c = [X x, Tinv y, Sinv y, H y, Tinv y, CNOT x y, X x, T y, H y, S y, T y, CNOT x y]
t13 x y = c ++ c
  where c = [CNOT x y, X x, T y, H y, T y, H y, Tinv y, CNOT x y, X x, T y, H y, Tinv y, H y, Tinv y]
t14 x y =
  [X x, CNOT x y, X x, T y, H y, T y, H y, Tinv y, CNOT x y, Sinv x, T y, H x, H y, Tinv x, S y, Tinv y,
   X y, CNOT y x, X y, T x, H x, T x, H x, Tinv x, CNOT y x, T x, T y, H x, Sinv y, S x, H y, Tinv x, Tinv y,
   CNOT x y, T y, H y, Tinv y, H y, Tinv y, X x, CNOT x y, X x, T y, T x, H y, Sinv x, S y, H x, Tinv x,
   CNOT y x, T x, H x, Tinv x, H x, Tinv x, X y, CNOT y x, X y, T x, H x, Sinv y, S x, H y, Tinv y]

verifyCliffordT () = sequence_ . map f $ onequbit ++ twoqubit
  where onequbit   = mapSnds ($ "x") [("t1", t1), ("t2", t2), ("t3", t3), ("t4", t4), ("t5", t5),
                                      ("t6", t6), ("t7", t7), ("t8", t8), ("t9", t9)]
        twoqubit   = mapSnds ($ "y") . mapSnds ($ "x") $ [("t10", t10), ("t11", t11), ("t12", t12),
                                                          ("t13", t13), ("t14", t14)]
        f (name, c) = case validateIsometry False ["x", "y"] ["x", "y"] c [] of
          Identity _ -> putStrLn $ "Successfully verified relation " ++ name
          _          -> putStrLn $ "ERROR: Failed to verify relation " ++ name
        mapSnds f xs    = map (mapSnd f) xs
        mapSnd f (a, b) = (a, f b)

-- Temp for writing experimental results
printVerStats circ =
  let (uids, m, c, t) = foldl' g (Set.empty,0,0,0) (map f circ) in do
    putStrLn $ "  n: " ++ show (Set.size uids)
    putStrLn $ "  m: " ++ show m
    putStrLn $ "  Clifford: " ++ show c
    putStrLn $ "  T/T*: " ++ show t
  where
    f gate = case gate of
      H x      -> (Set.singleton x, 1, 1, 0)
      X x      -> (Set.singleton x, 0, 1, 0)
      Y x      -> (Set.singleton x, 0, 1, 0)
      Z x      -> (Set.singleton x, 0, 1, 0)
      S x      -> (Set.singleton x, 0, 1, 0)
      Sinv x   -> (Set.singleton x, 0, 1, 0)
      T x      -> (Set.singleton x, 0, 0, 1)
      Tinv x   -> (Set.singleton x, 0, 0, 1)
      CNOT x y -> (Set.fromList [x,y], 0, 1, 0)
      Swap x y -> (Set.fromList [x,y], 0, 0, 0)
    g (uids1, m1, c1, t1) (uids2, m2, c2, t2) =
      (Set.union uids1 uids2, m1+m2, c1+c2, t1+t2)

-- Phase specifications
phaseSpec :: (Eq a, Num a) => [ID] -> a -> SOP a
phaseSpec xs v = SOP 0 inv [] (ofTerm v xs) outv
  where
    inv  = Map.fromList $ zip xs (repeat True)
    outv = Map.fromList $ [(q, ofVar q) | q <- xs]
