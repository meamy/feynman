{-# LANGUAGE ViewPatterns #-}

module Analysis.SOP where

import Text.Printf

import Data.Bits
import Data.Maybe
import Data.List
import Data.Monoid ((<>))

import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map

import Algebra.Polynomial
import Syntax hiding (toffoli, subst)
import qualified Syntax as Syntax

import Data.Ratio
import Data.Coerce

import Control.Monad
import Data.Function

import Test.QuickCheck
  
import Debug.Trace

{- Invariants:
   sort . Map.elems == Map.elems -}
data SOP a = SOP {
  sde      :: Int,
  inVals   :: Map ID Bool,
  pathVars :: [Int],
  poly     :: Multilinear a,
  outVals  :: Map ID (Multilinear Bool)
  } deriving (Eq)

instance (Show a, Eq a, Num a) => Show (SOP a) where
  show sop = printf "|%s> --> 1/sqrt(2)^%d Sum[%s] e^i*pi*{%s}|%s>" is (sde sop) pvars (show $ poly sop) os
    where is = concatMap (\(v, b) -> if b then v else "0") . Map.toList $ inVals sop
          os = concatMap showPoly $ Map.elems $ outVals sop
          pvars = intercalate "," . map (\i -> pathVar i) $ pathVars sop
          showPoly p
            | isMono p  = show p
            | otherwise = "(" ++ show p ++ ")"

pathVar :: Int -> ID
pathVar i = "p" ++ show i

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
  X x      -> init { outVals = Map.adjust (+ (constant True)) x outv }
  Y x      -> init { poly = p + (constant $ fromInteger 2) + (ofTerm (fromInteger 4) [x]),
                     outVals = Map.adjust (+ (constant True)) x outv }
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

isClosed :: SOP a -> Bool
isClosed = all not . Map.elems . inVals

isKet :: SOP a -> Bool
isKet = all ((< 1) . degree) . Map.elems . outVals

expandPaths :: (Eq a, Num a) => SOP a -> [SOP a]
expandPaths sop = case pathVars sop of
      []   -> [sop]
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant False) $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) (constant False)) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant True) $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) (constant True)) $ outVals sop }
        in
          expandPaths sop0 ++ expandPaths sop1

mapPaths :: (SOP Z8 -> Maybe DOmega) -> SOP Z8 -> Maybe DOmega
mapPaths f sop
  | not (isClosed sop) = Nothing
  | not (isKet sop)    = Nothing
  | otherwise          = case pathVars sop of
      []   -> Just $ scaledExp (sde sop) (getConstant $ poly sop)
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant False) $ poly sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant True) $ poly sop }
        in
          (+) <$> f sop0 <*> f sop1

mapPathsUnsafe :: (SOP Z8 -> DOmega) -> SOP Z8 -> DOmega
mapPathsUnsafe f sop = case pathVars sop of
      []   -> scaledExp (sde sop) (getConstant $ poly sop)
      x:xs ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant False) $ poly sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) (constant True) $ poly sop }
        in
          f sop0 + f sop1

amplitude0 :: SOP Z8 -> Maybe DOmega
amplitude0 = fix mapPaths

amplitude :: SOP Z8 -> Maybe DOmega
amplitude = mapPaths amplitude . reduce

amplitude0Unsafe :: SOP Z8 -> DOmega
amplitude0Unsafe = fix mapPathsUnsafe

amplitudeUnsafe :: SOP Z8 -> DOmega
amplitudeUnsafe = mapPathsUnsafe amplitudeUnsafe . reduce

{- Verification -}

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
axiomSimplify sop = msum . (map g) . filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop
        g i = if (pathVar i) `appearsIn` (poly sop) then Nothing else Just i

axiomHHStrict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHStrict sop = msum . (map h) . filter f $ pathVars sop
  where f i      = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop
        g (x, p) = x `elem` (map pathVar $ pathVars sop)
        h i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomHHOutputRestricted :: (Eq a, Fin a) => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHOutputRestricted sop = msum . (map h) . filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop
        g (x, p) = x `elem` (map pathVar $ pathVars sop) && degree p <= 1
        h i = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomSH3Strict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Multilinear Bool)
axiomSH3Strict sop = msum . (map g) . filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop
        g i =
          let p' = factorOut (pathVar i) $ (poly sop) - (ofTerm 2 [pathVar i]) in
            toBooleanPoly p' >>= \q -> Just (i, q)

-- Main axiom reduction function
applyAxiom :: (Eq a, Fin a) => SOP a -> Either (SOP a) (SOP a)
applyAxiom sop = case sop of
  (axiomSimplify -> Just rem) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [rem] }
  (axiomHHStrict -> Just (rem, sub, eq)) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [rem, sub],
          poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
          outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
  (axiomSH3Strict -> Just (rem, eq)) -> Right $
    sop { sde      = sde sop - 1,
          pathVars = pathVars sop \\ [rem],
          poly     = simplify $ constant 1 + distribute 6 eq + removeVar (pathVar rem) (poly sop)
        }
  _ -> Left sop

applyAxiomOutputRestricted :: (Eq a, Fin a) => SOP a -> Either (SOP a) (SOP a)
applyAxiomOutputRestricted sop = case sop of
  (axiomSimplify -> Just rem) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [rem] }
  (axiomHHOutputRestricted -> Just (rem, sub, eq)) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [rem, sub],
          poly     = simplify . subst (pathVar sub) eq . removeVar (pathVar rem) $ poly sop,
          outVals  = Map.map (simplify . subst (pathVar sub) eq) $ outVals sop }
  (axiomSH3Strict -> Just (rem, eq)) -> Right $
    sop { sde      = sde sop - 1,
          pathVars = pathVars sop \\ [rem],
          poly     = simplify $ constant 1 + distribute 6 eq + removeVar (pathVar rem) (poly sop)
        }
  _ -> Left sop

-- Strategies
reduce :: (Eq a, Fin a) => SOP a -> SOP a
reduce (flip (foldM (\sop _ -> applyAxiom sop)) [0..] -> Left sop) = sop

evaluate :: (Eq a, Fin a) => SOP a -> Map ID Bool -> Map ID Bool -> SOP a
evaluate sop ket bra = reduce $ restrict (ofKet ket <> sop) bra

cliffordTCrush :: SOP Z8 -> Map ID Bool -> Map ID Bool -> DOmega
cliffordTCrush sop ket bra = amplitudeUnsafe (restrict sop' bra)
  where fromLeft (Left x) = x
        sop' = fromLeft $ foldM (\sop _ -> applyAxiomOutputRestricted sop) (ofKet ket <> sop) [0..]

-- Main verification functions

verifySpec :: SOP Z8 -> [ID] -> [ID] -> [Primitive] -> Maybe (SOP Z8)
verifySpec spec vars inputs gates =
  let hConj   = map H inputs
      init    = blank vars
      sop     = circuitSOPWithHints vars (hConj ++ (dagger gates) ++ hConj)
      reduced = reduce (init <> sop <> spec)
  in
    case reduced == init of
      True  -> Nothing
      False -> Just reduced

validate :: [ID] -> [ID] -> [Primitive] -> [Primitive] -> Maybe (SOP Z8)
validate vars inputs c1 c2 =
  let sop     = circuitSOPWithHints vars (c1 ++ dagger c2)
      ket     = blank (vars \\ inputs)
      bra     = Map.mapWithKey (\v b -> if b then ofVar v else constant False) $ inVals (ket <> sop)
      reduced = reduce $ restrictGeneral (ket <> sop) bra
  in
    case reduced == (ket <> (identity vars)) of
      True  -> Nothing
      False -> Just reduced

{- Tests -}

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

cHSpec x y = SOP {
  sde      = 1,
  inVals   = Map.fromList [(x, True), (y, True)],
  pathVars = [0],
  poly     = ofTerm (Z8 4) [x, y, pathVar 0],
  outVals  = Map.fromList [(x, ofVar x), (y, ofVar y + ofTerm True [x, y] + ofTerm True [x, pathVar 0])]
  }

idHard x y = c ++ c
  where c = [X x, Tinv y, Sinv y, H y, Tinv y, CNOT x y, X x, T y, H y, S y, T y, CNOT x y]

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

toffoliSpec :: ID -> ID -> ID -> SOP Z8
toffoliSpec x y z = SOP {
  sde      = 0,
  inVals   = (Map.fromList [(x, True), (y, True), (z, True)]),
  pathVars = [],
  poly     = zero,
  outVals   = (Map.fromList [(x, ofVar x), (y, ofVar y), (z, ofVar z + ofTerm True [x,y])])
  }

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

toffoliNSpec :: [ID] -> SOP Z8
toffoliNSpec xs = SOP {
  sde      = 0,
  inVals   = Map.fromList $ [(x, True) | x <- xs] ++ [(y, False) | y <- anc],
  pathVars = [],
  poly     = zero,
  outVals  = Map.insert (last xs) product outInit
  }
  where anc     = ["_anc" ++ show i | i <- [0..length xs - 3]]
        product = ofVar (last xs) + ofTerm True (init xs)
        outInit = Map.fromList $ [(x, ofVar x) | x <- xs] ++ [(y, constant False) | y <- anc]

verifyToffoliN :: Int -> Maybe (SOP Z8)
verifyToffoliN n = verifySpec (toffoliNSpec inputs) vars inputs (toffoliN inputs)
  where inputs = take n $ map (\i -> [i]) ['a'..]
        vars   = inputs ++ ["_anc" ++ show i | i <- [0..n-3]]

-- General product gates
lst = [[x] | x <- ['a'..]]

genproduct :: [ID] -> [Primitive]
genproduct []       = []
genproduct (x:[])   = []
genproduct (x:z:[]) = [CNOT x z]
genproduct (x:xs)   =
  let z    = last xs
      conj = [CNOT z x, T z, Tinv x, CNOT z x]
  in
    [H z] ++ conj ++ genproduct xs ++ dagger conj ++ [H z]

testprod i = reduce $ circuitSOPWithHints (take i lst) $ genproduct (reverse $ take i lst)

genproduct1 :: [ID] -> [Primitive]
genproduct1 []         = []
genproduct1 (x:[])     = []
genproduct1 (x:z:[])   = [CNOT x z]
genproduct1 (x:y:z:[]) =
  let conj = [CNOT z x, T z, Tinv x, CNOT z x] in
    [H z] ++ conj ++ [CNOT y z] ++ dagger conj ++ [CNOT y z, H z]
genproduct1 (x:xs)     =
  let z    = last xs
      conj = [CNOT z x, T z, Tinv x, CNOT z x]
  in
    [H z] ++ conj ++ genproduct1 xs ++ dagger conj ++ [H z]

testprod1 i = reduce $ circuitSOPWithHints (take i lst) $ genproduct1 (reverse $ take i lst)

reltoff :: [ID] -> [Primitive]
reltoff []       = []
reltoff (x:[])   = []
reltoff (x:z:[]) = [CNOT x z]
reltoff (x:xs)   =
  let z    = last xs
      conj = [CNOT z x, T z, Tinv x, CNOT z x]
      spro = reltoff xs
      --corr = reltoff $ tail xs
  in
    [H z] ++ conj ++ spro ++ dagger conj ++ dagger spro ++ [H z]

testrel i = reduce $ circuitSOPWithHints (take i lst) $ reltoff (reverse $ take i lst)

toffoliNOneAnc :: [ID] -> [Primitive]
toffoliNOneAnc []         = []
toffoliNOneAnc (x:[])     = []
toffoliNOneAnc (x:z:[])   = [CNOT x z]
toffoliNOneAnc (x:y:z:[]) = toffoli x y z
toffoliNOneAnc l@(x:y:xs) =
  let anc = "_anc" ++ show 0
      pp1 = genproduct $ init l ++ [anc]
      pp2 = genproduct $ init xs ++ [anc]
  in
    pp1 ++ pp2 ++ [CNOT anc (last xs)] ++ (dagger pp2) ++ (dagger pp1)

maslov :: [ID] -> [Primitive]
maslov = go 0
  where go i []         = []
        go i (w:[])     = []
        go i (w:z:[])   = [CNOT w z]
        go i (w:x:z:[]) = toffoli w x z
        go i (w:x:y:xs) =
          let anc = "_anc" ++ show i
              sub = genproduct1 [w,x,y,anc]
          in
            sub ++ go (i+1) (anc:xs) ++ (dagger sub)

testmaslov i = reduce $ circuitSOPWithHints (take i lst ++ ["_anc" ++ show j | j <- [0..i-3]]) $ maslov (reverse $ take i lst)

verifyMaslovN :: Int -> Maybe (SOP Z8)
verifyMaslovN n = verifySpec (toffoliNSpec inputs) vars inputs (maslov inputs)
  where inputs = take n $ map (\i -> [i]) ['a'..]
        vars   = inputs ++ ["_anc" ++ show i | i <- [0..n-3]]

{-
relToff4 :: ID -> ID -> ID -> ID -> [Primitive]
relToff4 w x y z =
  [ H z,
    CNOT z y,
    T z,
    Tinv y,
    CNOT z y,
-}

genCCZ :: [String] -> Gen [Primitive]
genCCZ xs = do
  x <- elements xs
  y <- elements $ xs \\ [x]
  z <- elements $ xs \\ [x,y]
  return $ ccz x y z

genCZ :: [String] -> Gen [Primitive]
genCZ xs = do
  x <- elements xs
  y <- elements $ xs \\ [x]
  return $ cz x y

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
      cTrans = concat [cz (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      f' = (Syntax.subst sub g) ++ cTrans
      f  = xTrans ++ g ++ cTrans ++ xTrans
  return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

-- More tests

threeT x y z anc =
  [CNOT x y, CNOT x z] ++
  toffoli y z anc ++
  [CNOT x z, CNOT x anc, CNOT y z, T z, S anc, CNOT y z, CNOT x anc, CNOT x z] ++
  toffoli y z anc ++
  [CNOT x z, CNOT x y]

minimalProductGate []     t = []
minimalProductGate (c:[]) t = [CNOT c t]
minimalProductGate (c:cs) t = tmp ++ minimalProductGate cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate1 []         t = []
minimalProductGate1 (c:[])     t = [CNOT c t]
minimalProductGate1 (c1:c2:[]) t =
  [H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t, CNOT t c1, T c1, Tinv t, CNOT t c1, CNOT c2 t, H t]
minimalProductGate1 (c:cs)     t = tmp ++ minimalProductGate1 cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

minimalProductGate2 []         t = []
minimalProductGate2 (c:[])     t = [CNOT c t]
minimalProductGate2 (c1:c2:[]) t =
  [S t, H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t, CNOT t c1, T c1, Tinv t, CNOT t c1, CNOT c2 t, H t, Sinv t]
minimalProductGate2 (c:cs)     t = tmp ++ minimalProductGate2 cs t ++ dagger tmp
  where tmp = [S t, H t, CNOT t c, T t, Tinv c, CNOT t c] 

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
minimalProductGate5 (c:cs) t = tmp ++ minimalProductGate4 cs t ++ dagger tmp
  where tmp = [S t, H t, CNOT t c, Tinv c, CNOT t c] 

generalProductGate []     t = []
generalProductGate (c:[]) t = [CNOT c t]
generalProductGate (c:cs) t = [H t] ++ tmp ++ generalProductGate cs t ++ dagger tmp ++ dagger (generalProductGate cs t) ++ [H t]
  where tmp = [CNOT t c, T t, Tinv c, CNOT t c] 

generalProductGateN n []     t = []
generalProductGateN n (c:[]) t = [CNOT c t]
generalProductGateN n (c:cs) t
  | n == 0    = generalProductGate (c:cs) t
  | otherwise = tmp ++ generalProductGateN (n-1) cs t ++ dagger tmp
  where tmp = [H t, CNOT t c, T t, Tinv c, CNOT t c] 

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

{- Clifford identities -}

-- Defined gates
omega x = [T x, X x, T x, X x]

c1 x = concat $ replicate 8 (omega x)
  
c2 x = [H x, H x]
c3 x = [S x, S x, S x, S x]
c4 x = [S x, H x, S x, H x, S x] ++ dagger (omega x)

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

verifyClifford _ = sequence_ . map f $ onequbit ++ twoqubit ++ threequbit
  where onequbit   = mapSnds ($ "x") [("c1", c1), ("c2", c2), ("c3", c3), ("c4", c4)]
        twoqubit   = mapSnds ($ "y") . mapSnds ($ "x") $ [("c5", c5), ("c6", c6), ("c7", c7), ("c8", c8),
                                                          ("c9", c9), ("c10", c10), ("c11", c11)]
        threequbit = mapSnds ($ "z") . mapSnds ($ "y") . mapSnds ($ "x") $ [("c12", c12), ("c13", c13),
                                                                            ("c14", c14), ("c15", c15)]
        f (name, c) = case validate ["x", "y", "z"] ["x", "y", "z"] c [] of
          Nothing -> return ()
          _       -> putStrLn $ "Error: failed to verify " ++ name
        mapSnds f xs    = map (mapSnd f) xs
        mapSnd f (a, b) = (a, f b)
