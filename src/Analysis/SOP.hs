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
import Syntax hiding (toffoli)

import Data.Ratio
import Data.Coerce

import Control.Monad

import Debug.Trace

{- Invariants:
   sort . Map.elems == Map.elems -}
data SOP a = SOP {
  dim      :: Int,
  sde      :: Int,
  inVals   :: Map ID (Maybe Int),
  pathVars :: [Int],
  poly     :: Multilinear a,
  outVals  :: Map ID (Multilinear Bool)
  } deriving (Eq)

instance (Show a, Eq a, Num a) => Show (SOP a) where
  show sop = printf "|%s> --> 1/sqrt(2)^%d Sum[%s] e^i*pi*{%s}|%s>" is (sde sop) pvars (show $ poly sop) os
    where is = concatMap (showPoly . (maybe (zero :: Multilinear Bool) ofVar)) $ Map.elems $ inVals sop
          os = concatMap showPoly $ Map.elems $ outVals sop
          pvars = intercalate "," $ map (\i -> "x" ++ show i) (pathVars sop)
          showPoly p
            | isMono p  = show p
            | otherwise = "(" ++ show p ++ ")"

valid :: SOP a -> Bool
valid sop = (dim sop) + (length . pathVars $ sop) == (vars . poly $ sop)

{- Constructors -}

identity0 :: SOP a
identity0 = SOP 0 0 Map.empty [] zero Map.empty

identity :: [ID] -> SOP a
identity vars = SOP {
  dim      = length vars,
  sde      = 0,
  inVals   = Map.fromList $ zip vars [Just i | i <- [0..]],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [ofVar i | i <- [0..]]
  }

blank :: [ID] -> SOP a
blank vars = SOP {
  dim      = 0,
  sde      = 0,
  inVals   = Map.fromList $ zip vars [Nothing | i <- [0..]],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [zero | i <- [0..]]
  }

{- Operators -}
-- FIXME: ofMultilinear sometimes gets called with n< number of vars
extendFrame :: Map ID (Maybe Int) -> SOP a -> SOP a
extendFrame vals sop@(SOP dim sde ivals pvars p ovals) = SOP dim' sde ivals' pvars' p' ovals'
  where
    (dim', ivals') =
      let f dim v = case v of
            Just _  -> (dim+1, Just dim)
            Nothing -> (dim, Nothing)
      in
        Map.mapAccum f 0 $ Map.union ivals vals
    sub =
      let qv = mapMaybe (\(k, mi) -> mi >>= \i -> return (i, fromJust $ ivals'!k)) . Map.toAscList $ ivals
          pv = zip pvars pvars'
      in
        Map.fromAscList $ qv ++ pv
    pvars' = map (+ (dim' - dim)) pvars
    p' = ofMultilinear sub (dim' + length pvars) p
    ovals' =
      let f k v = case ovals!?k of
                    Just poly -> ofMultilinear sub (dim' + length pvars) poly
                    Nothing   -> maybe zero ofVar $ v
      in
        Map.mapWithKey f ivals'

compose :: (Eq a, Num a) => SOP a -> SOP a -> SOP a
compose u v
  | u == mempty = v
  | v == mempty = u
  | otherwise   = composeUnsafe (extendFrame (inVals v) u) v

-- Assumes Map.keys istate' `subset` Map.keys istate
composeUnsafe :: (Eq a, Num a) => SOP a -> SOP a -> SOP a
composeUnsafe u@(SOP dim sde istate pvars p ostate) v@(SOP dim' sde' istate' pvars' p' ostate') =
  SOP dim (sde + sde') istate (pvars ++ pvars'') (simplify $ p + p'') ostate''
  where sub      = Map.foldlWithKey' (\sub q (Just i) -> Map.insert i (ostate!q) sub) Map.empty istate'
        subp     = substMany sub . addVars (vars p - dim') dim'
        pvars''  = map (+ max 0 (vars p - dim')) pvars'
        p''      = substMany sub . addVars (vars p - dim') dim' $  p'
        ostate'' = Map.union (Map.map (simplify . substMany sub . addVars (vars p - dim') dim') ostate') ostate


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
  where init@(SOP num s inv pathv p outv) = identity $ sort vars

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
axiomSimplify sop = msum . (map f) . filter (\i -> all (not . (i `appearsIn`)) out) $ pathVars sop
  where f x = if x `appearsIn` (poly sop) then Nothing else Just x
        out = Map.elems $ outVals sop

axiomHHStrict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Int, Multilinear Bool)
axiomHHStrict sop = msum . (map f) . filter (\i -> all (not . (i `appearsIn`)) out) $ pathVars sop
  where f x = return (factorOut x $ poly sop) >>= toBooleanPoly >>= getSubst >>= \(y, psub) -> Just (x, y, psub)
        out = Map.elems $ outVals sop

axiomSH3Strict :: (Eq a, Fin a) => SOP a -> Maybe (Int, Multilinear Bool)
axiomSH3Strict sop = msum . (map f) . filter (\i -> all (not . (i `appearsIn`)) out) $ pathVars sop
  where f x = return (factorOut x $ (poly sop) - (ofTerm 2 [x])) >>= toBooleanPoly >>= \q -> Just (x, q)
        out = Map.elems $ outVals sop

-- Main axiom reduction function
applyAxiom :: (Eq a, Fin a) => SOP a -> Either (SOP a) (SOP a)
applyAxiom sop = case sop of
  (axiomSimplify -> Just xrem) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [xrem] }
  (axiomHHStrict -> Just (xrem, xsub, xeq)) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [xrem, xsub],
          poly     = simplify . subst xsub xeq . removeVar xrem $ poly sop,
          outVals  = Map.map (simplify . subst xsub xeq) $ outVals sop }
  (axiomSH3Strict -> Just (xrem, xeq)) -> Right $
    sop { sde = sde sop - 1,
          pathVars = pathVars sop \\ [xrem],
          poly     =
            let r = removeVar xrem $ poly sop in
                simplify $ constant 1 + distribute (vars $ poly sop) 6 xeq + r }
  _ -> Left sop

reduce :: (Eq a, Fin a) => SOP a -> SOP a
reduce (flip (foldM (\sop _ -> applyAxiom sop)) [0..] -> Left sop) = sop


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

-- If the sum-over-paths is verifiably unitary, we only need to check the |00...0> output state
unitaryTrans :: SOP Z8 -> SOP Z8
unitaryTrans sop = foldl' f sop (Map.keys $ inVals sop)
  where f sop x = case getSubst ((outVals sop)!x) of
          Nothing        -> sop
          Just (y, psub) -> sop { pathVars = pathVars sop \\ [y],
                                  poly     = simplify . subst y psub $ poly sop,
                                  outVals  = Map.map (simplify . subst y psub) $ outVals sop }

validate :: [ID] -> [ID] -> [Primitive] -> [Primitive] -> Maybe (SOP Z8)
validate vars inputs c1 c2 =
  let hConj   = map H inputs
      init    = blank $ Map.keys (inVals sop)
      sop     = circuitSOPWithHints vars (hConj ++ c1 ++ dagger c2 ++ hConj)
      reduced = reduce (init <> sop)
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

cH = [ Sinv "y", H "y", Tinv "y", CNOT "x" "y", T "y", H "y", S "y"]

omeg = [ S "x", H "x", S "x", H "x", S "x", H "x" ]

cT = [H "z", Sinv "x", CNOT "x" "y", CNOT "y" "z", CNOT "z" "x", T "x", Tinv "z",
      CNOT "y" "x", CNOT "y" "z", T "x", Tinv "z", CNOT "x" "z", H "x", T "x", H "x",
      CNOT "x" "z", Tinv "x", T "z", CNOT "y" "z", CNOT "y" "x", Tinv "x", T "z",
      CNOT "z" "x", CNOT "y" "z", CNOT "x" "y", S "x", H "z"]

ids = ["x", "y", "z"]
soptof = circuitSOPWithHints ids tof

soptoffoli :: SOP Z8
soptoffoli = SOP {
  dim      = 3,
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
  dim      = 3,
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
  dim      = length xs,
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
    
