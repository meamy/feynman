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
              case solveForX (map pathVar $ pathVars sop) (constant (bra!x) + x') of
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
              case solveForX (map pathVar $ pathVars sop) (constant (bra!x) + x') of
                Nothing        -> sop
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
    | n == m = D ((a + b) `div` 2, n-1)
    | otherwise =
      let n' = max n m in
        D (a * 2^(n' - n) + b * 2^(n' - m), n')
  (D (a,n)) * (D (b,m)) = D (a * b, n + m)
  negate (D (a,n)) = D (-a, n)
  abs (D (a,n))    = D (abs a, n)
  signum (D (a,n)) = D (signum a, 0)
  fromInteger i    = D (fromInteger i, 0)

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
axiomHHStrict sop = msum . (map g) . filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop
        g i = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- solveForX (map pathVar $ pathVars sop) p''
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

reduce :: (Eq a, Fin a) => SOP a -> SOP a
reduce (flip (foldM (\sop _ -> applyAxiom sop)) [0..] -> Left sop) = sop

-- Applies reduction axioms to evaluate an SOP form
evaluate :: (Eq a, Fin a) => SOP a -> Map ID Bool -> Map ID Bool -> SOP a
evaluate sop ket bra = reduce $ restrict (ofKet ket <> sop) bra

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
  let hConj   = map H inputs
      ket     = Map.fromList [(v, False) | v <- Map.keys (inVals sop)]
      sop     = circuitSOPWithHints vars (hConj ++ c1 ++ dagger c2 ++ hConj)
      reduced = evaluate sop ket ket
  in
    case reduced == blank (Map.keys $ inVals sop) of
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
