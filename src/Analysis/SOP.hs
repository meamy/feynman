{-# LANGUAGE ViewPatterns #-}

module Analysis.SOP where

import Text.Printf

import Data.Bits
import Data.Maybe
import Data.List
import Data.Monoid ((<>))

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Algebra.Polynomial
import Syntax hiding (toffoli)

import Data.Ratio
import Data.Coerce

import Control.Monad

data SOP a = SOP {
  n        :: Int,
  sde      :: Int,
  inVals   :: Map ID (Maybe Int),
  pathVars :: [Int],
  poly     :: Multilinear a,
  outVals  :: Map ID (Multilinear Bool)
  } deriving (Eq)

instance (Show a, Eq a, Num a) => Show (SOP a) where
  show sop = printf "|%s> --> 1/sqrt(2)^%d Sum e^i*pi*{%s}|%s>" is (sde sop) (show $ poly sop) os
    where is = concatMap (showPoly . (maybe (zero :: Multilinear Bool) ofVar)) $ Map.elems $ inVals sop
          os = concatMap showPoly $ Map.elems $ outVals sop
          showPoly p
            | isMono p  = show p
            | otherwise = "(" ++ show p ++ ")"

{- Constructors -}

identity0 :: SOP a
identity0 = SOP 0 0 Map.empty [] zero Map.empty

identity :: [ID] -> SOP a
identity vars = SOP {
  n        = length vars,
  sde      = 0,
  inVals   = Map.fromList $ zip vars [Just i | i <- [0..]],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [ofVar i | i <- [0..]]
  }

blank :: [ID] -> SOP a
blank vars = SOP {
  n        = length vars,
  sde      = 0,
  inVals   = Map.fromList $ zip vars [Nothing | i <- [0..]],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [zero | i <- [0..]]
  }

{- Operators -}

-- For now, compose assumes both sum-over-paths are defined over the same qubits.
-- This is fine for now and in fact faster, but not very flexible.
-- It is also assumed that the path variables are sorted requires the mapped IDs to be the same in either.
compose :: (Eq a, Num a) => SOP a -> SOP a -> SOP a
compose u@(SOP n sde istate pvars p ostate) v@(SOP n' sde' istate' pvars' p' ostate')
  | u == mempty = v
  | v == mempty = u
  | otherwise  = SOP n (sde + sde') istate (pvars ++ pvars'') (simplify $ p + p'') ostate''
  where sub      = Map.foldlWithKey' (\sub q (Just i) -> Map.insert i (ostate!q) sub) Map.empty istate'
        pvars''  = map (+ length pvars) pvars'
        p''      = substMany sub $ addVars (length pvars) n p'
        ostate'' = Map.map (simplify . substMany sub . addVars (length pvars) n) ostate'

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

sopCliffordT :: [ID] -> Primitive -> SOP Z8
sopCliffordT vars gate = case gate of
  H x      -> init { pathVars = [num],
                     sde = s + 1,
                     poly = p + ofTerm (fromInteger 4) [fromJust (inv!x), num],
                     outVals = Map.insert x (ofVar num) outv }
  X x      -> init { outVals = Map.adjust (+ (constant True)) x outv }
  Y x      -> init { poly = p + (constant $ fromInteger 2) + (ofTerm (fromInteger 4) [fromJust $ inv!x]),
                     outVals = Map.adjust (+ (constant True)) x outv }
  Z x      -> init { poly = p + (ofTerm (fromInteger 4) [fromJust $ inv!x]) }
  CNOT x y -> init { outVals = Map.adjust (+ (ofVar (fromJust $ inv!x))) y outv }
  S x      -> init { poly = p + (ofTerm (fromInteger 2) [fromJust $ inv!x]) }
  Sinv x   -> init { poly = p + (ofTerm (fromInteger 6) [fromJust $ inv!x]) }
  T x      -> init { poly = p + (ofTerm (fromInteger 1) [fromJust $ inv!x]) }
  Tinv x   -> init { poly = p + (ofTerm (fromInteger 7) [fromJust $ inv!x]) }
  Swap x y -> init { outVals = Map.insert x (outv!y) $ Map.insert y (outv!x) outv }
  where init@(SOP num s inv pathv p outv) = identity vars

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

toBooleanPoly :: Fin a => Multilinear a -> Maybe (Multilinear Bool)
toBooleanPoly = convertMaybe injectZ2

axiomHHStrict :: Fin a => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHStrict sop = msum . (map f) . filter (\i -> all (not . (i `appearsIn`)) out) $ pathVars sop
  where f x = return (factorOut x $ poly sop) >>= toBooleanPoly >>= getSubst >>= \(y, psub) -> Just (x, y, psub)
        out = Map.elems $ outVals sop

daggerGate :: Primitive -> Primitive
daggerGate x = case x of
  H _      -> x
  X _      -> x
  Y _      -> x -- WARNING: this is incorrect
  CNOT _ _ -> x
  S x      -> Sinv x
  Sinv x   -> S x
  T x      -> Tinv x
  Tinv x   -> T x
  Swap _ _ -> x

dagger :: [Primitive] -> [Primitive]
dagger = reverse . map daggerGate

-- Main axiom reduction function
applyAxiom :: (Eq a, Fin a) => SOP a -> Either (SOP a) (SOP a)
applyAxiom sop = case sop of
  (axiomHHStrict -> Just (xrem, xsub, xeq)) -> Right $
    sop { sde      = sde sop - 2,
            pathVars = pathVars sop \\ [xrem, xsub],
            poly     = simplify . subst xsub xeq . removeVar xrem $ poly sop,
            outVals  = Map.map (simplify . subst xsub xeq) $ outVals sop }
  _ -> Left sop

reduce :: (Eq a, Fin a) => SOP a -> SOP a
reduce (flip (foldM (\sop _ -> applyAxiom sop)) [0..] -> Left sop) = sop

-- Main verification function
verifySpec :: SOP Z8 -> [ID] -> [ID] -> [Primitive] -> Maybe (SOP Z8)
verifySpec spec vars inputs gates =
  let hConj      = map H inputs
      init       = blank vars
      circuitSOP = foldMap (sopCliffordT vars) (hConj ++ (dagger gates) ++ hConj)
      reduced    = reduce (init <> circuitSOP <> spec)
  in
    case reduced == init of
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

ids = ["x", "y", "z"]
soptof = foldMap (sopCliffordT ids) tof

soptoffoli :: SOP Z8
soptoffoli = SOP {
  n        = 3,
  sde      = 0,
  inVals   = (Map.fromList [("x", Just 0), ("y", Just 1), ("z", Just 2)]),
  pathVars = [],
  poly     = zero,
  outVals   = (Map.fromList [("x", ofVar 0), ("y", ofVar 1), ("z", ofVar 2 + ofTerm True [0,1])])
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

toffoliSpec :: ID -> ID -> ID -> SOP Z8
toffoliSpec x y z = SOP {
  n        = 3,
  sde      = 0,
  inVals   = (Map.fromList [(x, Just 0), (y, Just 1), (z, Just 2)]),
  pathVars = [],
  poly     = zero,
  outVals   = (Map.fromList [(x, ofVar 0), (y, ofVar 1), (z, ofVar 2 + ofTerm True [0,1])])
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
  n        = 2*(length xs) - 3,
  sde      = 0,
  inVals   = Map.fromList $ (zip (xs ++ anc) [Just i | i <- [0..]]),
  pathVars = [],
  poly     = zero,
  outVals  = Map.insert (last xs) product $ Map.fromList $ zip (xs ++ anc) [ofVar i | i <- [0..]]
  }
  where anc = ["_anc" ++ show i | i <- [0..length xs - 3]]
        product = ofVar (length xs - 1) + (foldr (\i p -> ofVar i * p) one [0..length xs - 2])

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

testprod i = reduce $ foldMap (sopCliffordT $ take i lst) $ genproduct (reverse $ take i lst)

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

testprod1 i = reduce $ foldMap (sopCliffordT $ take i lst) $ genproduct1 (reverse $ take i lst)

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

testrel i = reduce $ foldMap (sopCliffordT $ take i lst) $ reltoff (reverse $ take i lst)

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

testmaslov i = reduce $ foldMap (sopCliffordT $ take i lst ++ ["_anc" ++ show j | j <- [0..i-3]]) $ maslov (reverse $ take i lst)

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
    
