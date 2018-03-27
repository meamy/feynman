{-# LANGUAGE ViewPatterns #-}

module Feynman.Verification.SOP where

import Text.Printf

import Data.Bits
import Data.Maybe
import Data.List
import Data.Monoid hiding ((<>))
import Data.Semigroup

import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map

import Feynman.Algebra.Base
import Feynman.Algebra.Linear hiding (identity)
import Feynman.Algebra.Polynomial
import Feynman.Core hiding (toffoli, subst)
import qualified Feynman.Core as Core

import Data.Ratio
import Data.Coerce

import Control.Monad
import Data.Function

import Test.QuickCheck
  
import Debug.Trace

import Data.Set (Set)
import qualified Data.Set as Set

{- Invariants:
   sort . Map.elems == Map.elems -}
data SOP a = SOP {
  sde      :: Int,
  inVals   :: Map ID Bool,
  pathVars :: [Int],
  poly     :: Multilinear a,
  outVals  :: Map ID (Multilinear Z2)
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
            | isMono p  = show p
            | otherwise = "(" ++ show p ++ ")"

pathVar :: Int -> ID
pathVar i = "p" ++ show i

internalPaths :: SOP a -> [Int]
internalPaths sop = filter f $ pathVars sop
  where f i = all (not . (appearsIn $ pathVar i)) . Map.elems $ outVals sop

{- Constructors -}

identity0 :: (Eq a, Ring a) => SOP a
identity0 = SOP 0 Map.empty [] zero Map.empty

identity :: (Eq a, Ring a) => [ID] -> SOP a
identity vars = SOP {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [True | v <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [ofVar v | v <- vars]
  }

identityTrans :: (Eq a, Ring a) => Map ID Bool -> SOP a
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

blank :: (Eq a, Ring a) => [ID] -> SOP a
blank vars = SOP {
  sde      = 0,
  inVals   = Map.fromList $ zip vars [False | i <- vars],
  pathVars = [],
  poly     = zero,
  outVals  = Map.fromList $ zip vars [zero | i <- vars]
  }

ofKet :: (Eq a, Ring a) => Map ID Z2 -> SOP a
ofKet ket = SOP {
  sde      = 0,
  inVals   = Map.map (\_ -> False) ket,
  pathVars = [],
  poly     = zero,
  outVals  = Map.map constant ket
  }


{- Operators -}
compose :: (Eq a, Ring a) => SOP a -> SOP a -> SOP a
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

restrict :: (Eq a, Ring a) => SOP a -> Map ID Z2 -> SOP a
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

tryRestrict :: (Eq a, Ring a) => SOP a -> Map ID Z2 -> SOP a
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

restrictGeneral :: (Eq a, Ring a) => SOP a -> Map ID (Multilinear Z2) -> SOP a
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
      
instance (Eq a, Ring a) => Semigroup (SOP a) where
  a <> b = compose a b

instance (Eq a, Ring a) => Monoid (SOP a) where
  mempty  = identity0
  mappend = compose

{- Implementations -}

toSOPWithHints :: [ID] -> Primitive -> SOP Dyadic
toSOPWithHints vars gate = case gate of
  H x      -> init { pathVars = [0],
                     sde = s + 1,
                     poly = p + ofTerm (dyadic 1 1) [x, "p0"],
                     outVals = Map.insert x (ofVar "p0") outv }
  X x      -> init { outVals = Map.adjust (+ one) x outv }
  Y x      -> init { poly = p + (constant $ dyadic 1 2) + (ofTerm (dyadic 1 1) [x]),
                     outVals = Map.adjust (+ one) x outv }
  Z x      -> init { poly = p + (ofTerm (dyadic 1 1) [x]) }
  CNOT x y -> init { outVals = Map.adjust (+ (ofVar x)) y outv }
  S x      -> init { poly = p + (ofTerm (dyadic 1 2) [x]) }
  Sinv x   -> init { poly = p + (ofTerm (dyadic 3 2) [x]) }
  T x      -> init { poly = p + (ofTerm (dyadic 1 3) [x]) }
  Tinv x   -> init { poly = p + (ofTerm (dyadic 7 3) [x]) }
  Swap x y -> init { outVals = Map.insert x (outv!y) $ Map.insert y (outv!x) outv }
  Rz (Discrete d) x -> init { poly = p + (ofTerm d [x]) }
  where init@(SOP s inv pathv p outv) = identity vars

toSOP :: Primitive -> SOP Dyadic 
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
  Rz _ x   -> toSOPWithHints [x] gate


circuitSOPWithHints :: [ID] -> [Primitive] -> SOP Dyadic
circuitSOPWithHints vars circuit = foldMap (toSOPWithHints vars) circuit

circuitSOP :: [Primitive] -> SOP Dyadic
circuitSOP circuit = foldMap toSOP circuit

{- Expansions -}

isClosed :: (Eq a, Ring a) => SOP a -> Bool
isClosed = (< 1) . degree . poly

foldPaths :: (Eq a, Ring a) => (SOP a -> b) -> (b -> b -> b) -> SOP a -> b
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
          trace ("  expanding at " ++ (pathVar x)) $
          g (foldPaths f g sop0) (foldPaths f g sop1)

foldReduce :: (SOP Dyadic-> b) -> (b -> b -> b) -> SOP Dyadic -> b
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
          trace ("  expanding at " ++ (pathVar x)) $
          g (foldReduce f g $ reduce sop0) (foldReduce f g $ reduce sop1)

foldReduceFull :: (SOP Dyadic -> b) -> (b -> b -> b) -> SOP Dyadic -> b
foldReduceFull f g sop = case (pathVars sop, vars $ poly sop) of
      ([], []) -> f sop
      ([], x:xs) ->
        let sop0 = sop { poly = simplify . subst x zero $ poly sop,
                         outVals = Map.map (simplify . subst x zero) $ outVals sop }
            sop1 = sop { poly = simplify . subst x one $ poly sop,
                         outVals = Map.map (simplify . subst x one) $ outVals sop }
        in
          trace ("  expanding basis value at " ++ x) $
          g (foldReduceFull f g $ reduce sop0) (foldReduceFull f g $ reduce sop1)
      (x:xs, _) ->
        let sop0 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) zero $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) zero) $ outVals sop }
            sop1 = sop { pathVars = xs,
                         poly = simplify . subst (pathVar x) one $ poly sop,
                         outVals = Map.map (simplify . subst (pathVar x) one) $ outVals sop }
        in
          trace ("  expanding at " ++ (pathVar x)) $
          g (foldReduceFull f g $ reduce sop0) (foldReduceFull f g $ reduce sop1)

expandPaths :: (Eq a, Ring a) => SOP a -> [SOP a]
expandPaths = foldPaths (\x -> [x]) (++)

amplitudesMaybe :: SOP Dyadic -> Maybe (Map (Map ID (Multilinear Z2)) DOmega)
amplitudesMaybe sop = foldReduce f g sop
  where f sop = if isClosed sop then
                    Just $ Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
                  else
                    Nothing
        g = liftM2 (Map.unionWith (+))

amplitudes :: SOP Dyadic -> Map (Map ID (Multilinear Z2)) DOmega
amplitudes sop = foldReduceFull f g sop
  where f sop = Map.fromList [(outVals sop, scaledExp (sde sop) . getConstant . poly $ sop)]
        g = Map.unionWith (+)

{- Verification -}

toBooleanPoly :: (Eq a, Periodic a, Ring a) => Multilinear a -> Maybe (Multilinear Z2)
toBooleanPoly = convertMaybe injectZ2 . simplify

axiomSimplify :: (Eq a, Periodic a) => SOP a -> Maybe Int
axiomSimplify sop = msum . (map f) $ internalPaths sop
  where f i = if (pathVar i) `appearsIn` (poly sop) then Nothing else Just i

axiomHHStrict :: (Eq a, Periodic a, Ring a) => SOP a -> Maybe (Int, Int, Multilinear Z2)
axiomHHStrict sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop)
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomHHOutputRestricted :: (Eq a, Periodic a, Ring a) => SOP a -> Maybe (Int, Int, Multilinear Z2)
axiomHHOutputRestricted sop = msum . (map f) $ internalPaths sop
  where g (x, p) = x `elem` (map pathVar $ pathVars sop) && degree p <= 1
        f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          (j, psub) <- find g $ solveForX p''
          return (i, read $ tail j, psub)

axiomSH3Strict :: SOP Dyadic -> Maybe (Int, Multilinear Z2)
axiomSH3Strict sop = msum . (map f) $ internalPaths sop
  where f i =
          let p' = factorOut (pathVar i) $ (poly sop) - (ofTerm (dyadic 1 2) [pathVar i]) in
            toBooleanPoly p' >>= \q -> Just (i, q)

axiomUnify :: SOP Dyadic -> Maybe (ID, Int, Multilinear Z2, Int, Multilinear Z2)
axiomUnify sop = msum . (map f) $ internal
  where internal   = internalPaths sop
        findSoln i = find (\(x, _) -> x == pathVar i) . solveForX
        f i        = do
          p'      <- return $ factorOut (pathVar i) $ poly sop
          (m, _)  <- find (\(m, a) -> monomialDegree m == 1 && order a == 4) . Map.toList . terms $ p'
          x       <- find (\v -> not (v == pathVar i)) $ monomialVars m
          p1      <- toBooleanPoly (p' - (ofTerm (dyadic 1 2) [x]))
          msum . (map $ g p' i x p1) $ internal \\ [i]
        g p' i x p1 j = do
          p''       <- return $ factorOut (pathVar j) $ poly sop
          p2        <- toBooleanPoly (p'' - (constant (dyadic 1 2)) - (ofTerm (dyadic 3 2) [x]))
          (_, jsub) <- findSoln j (subst x zero p1)
          (_, isub) <- findSoln i (subst x one p2)
          return (x, i, isub, j, jsub)

axiomKill :: (Eq a, Periodic a, Ring a) => SOP a -> Maybe ()
axiomKill sop = msum . (map f) $ internalPaths sop
  where f i      = do
          p'        <- return $ factorOut (pathVar i) $ poly sop
          p''       <- toBooleanPoly p'
          if intersect (vars p'') (map pathVar $ pathVars sop) == []
            then Just ()
            else Nothing

-- Main axiom reduction function
applyAxiom :: SOP Dyadic -> Either (SOP Dyadic) (SOP Dyadic)
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
          poly     = simplify $ one + distribute (dyadic 3 2) eq + removeVar (pathVar rem) (poly sop)
        }
  (axiomUnify     -> Just (x, i, isub, j, jsub)) -> Right $
    sop { sde      = sde sop - 2,
          pathVars = pathVars sop \\ [i, j],
          poly     =
            let xp = ofVar x
                pi = subst (pathVar j) jsub . subst x zero . removeVar (pathVar i) $ poly sop
                pj = subst (pathVar i) isub . subst x one  . removeVar (pathVar j) $ poly sop
            in
              simplify $ xp*pj + pi - xp*pi
        }
  _ -> Left sop

applyAxiomOutputRestricted :: SOP Dyadic -> Either (SOP Dyadic) (SOP Dyadic)
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
          poly     = simplify $ one + distribute (dyadic 3 2) eq + removeVar (pathVar rem) (poly sop)
        }
  _ -> Left sop

-- Strategies
reduce :: SOP Dyadic -> SOP Dyadic
reduce (flip (foldM (\sop _ -> applyAxiom sop)) [0..] -> Left sop) = sop

evaluate :: SOP Dyadic -> Map ID Z2 -> Map ID Z2 -> SOP Dyadic
evaluate sop ket bra = reduce $ restrict (ofKet ket <> sop) bra

-- Main verification functions

verifySpec :: SOP Dyadic -> [ID] -> [ID] -> [Primitive] -> Maybe (SOP Dyadic)
verifySpec spec vars inputs gates =
  let sop     = circuitSOPWithHints vars (dagger gates)
      reduced = reduce $ (spec <> sop)
  in
    case reduced == identityTrans (inVals spec) of
      True  -> Nothing
      False -> Just reduced

validate :: [ID] -> [ID] -> [Primitive] -> [Primitive] -> Maybe (SOP Dyadic)
validate vars inputs c1 c2 =
  let sop     = circuitSOPWithHints vars (c1 ++ dagger c2)
      ket     = blank (vars \\ inputs)
      bra     = Map.mapWithKey (\v b -> if b then ofVar v else zero) $ inVals (ket <> sop)
      reduced = reduce $ restrictGeneral (ket <> sop) bra
  in
    if reduced == identityTrans (inVals $ ket <> sop)
    then Nothing
    else case (axiomKill reduced, all (== one) . Map.elems $ amplitudes reduced) of
      (Just _, _) -> Just reduced
      (_, False)  -> Just reduced
      (_, _)      -> Nothing

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

cTSpec x y z = SOP {
  sde      = 0,
  inVals   = Map.fromList [(x, True), (y, True), (z, False)],
  pathVars = [],
  poly     = ofTerm (dyadic 1 3) [x, y],
  outVals  = Map.fromList [(x, ofVar x), (y, ofVar y), (z, zero)]
  }

cHSpec x y = SOP {
  sde      = 1,
  inVals   = Map.fromList [(x, True), (y, True)],
  pathVars = [0],
  poly     = ofTerm (dyadic 1 1) [x, y, pathVar 0],
  outVals  = Map.fromList [(x, ofVar x), (y, ofVar y + ofTerm one [x, y] + ofTerm one [x, pathVar 0])]
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

toffoliNSpec :: [ID] -> SOP Dyadic 
toffoliNSpec xs = SOP {
  sde      = 0,
  inVals   = Map.fromList $ [(x, True) | x <- xs] ++ [(y, False) | y <- anc],
  pathVars = [],
  poly     = zero,
  outVals  = Map.insert (last xs) product outInit
  }
  where anc     = ["_anc" ++ show i | i <- [0..length xs - 4]]
        product = ofVar (last xs) + ofTerm one (init xs)
        outInit = Map.fromList $ [(x, ofVar x) | x <- xs] ++ [(y, zero) | y <- anc]

verifyToffoliN n () = do
  putStrLn $ "Verifying Toffoli, N=" ++ show n
  printVerStats (toffoliN inputs)
  case verifySpec (toffoliNSpec inputs) vars inputs (toffoliN inputs) of
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ map (\i -> [i]) ['a'..]
        vars   = inputs ++ ["_anc" ++ show i | i <- [0..n-4]]

-- General product gates
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
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
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

adderOOPSpec :: Int -> [ID] -> [ID] -> [ID] -> SOP Dyadic
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
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
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
      f' = (Core.subst sub g) ++ cTrans
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
      f' = (Core.subst sub g) ++ cTrans
      f  = xTrans ++ g ++ cTrans ++ xTrans
  return $ hTrans ++ f ++ hTrans ++ f' ++ hTrans
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

hiddenShiftSpec :: Int -> [String] -> SOP Dyadic 
hiddenShiftSpec n string = SOP {
  sde      = 0,
  inVals   = Map.fromList [("x" ++ show i, False) | i <- [0..n-1]],
  pathVars = [],
  poly     = zero,
  outVals  =
     let f v = (v, if v `elem` string then one else zero) in
       Map.fromList $ map f ["x" ++ show i | i <- [0..n-1]]
  }

hiddenShiftQuantumSpec :: Int -> SOP Dyadic 
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
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
  where vars   = ["x" ++ show i | i <- [0..n-1]]

verifyHiddenShiftQuantum n a () = do
  putStrLn $ "Verifying random Symbolic Shift, n=" ++ show n ++ ", A=" ++ show a
  circ <- generate $ hiddenShiftQuantum n a
  printVerStats (circ)
  case verifySpec (hiddenShiftQuantumSpec n) vars inputs circ of
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
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
  
{- Quantum Fourier Transform -}

controlledRm m x y = [Rz (Discrete (dyadic 1 (m+1))) x,
                      Rz (Discrete (dyadic 1 (m+1))) y,
                      CNOT x y,
                      Rz (Discrete (dyadic (-1) (m+1))) y,
                      CNOT x y]

qft []     = []
qft (x:xs) = [H x] ++ concatMap f (zip [2..] xs) ++ qft xs
  where f (m, y) = controlledRm m x y

qftSpec :: [ID] -> SOP Dyadic
qftSpec xs = SOP {
  sde      = length xs,
  inVals   = Map.fromList $ [(x, True) | x <- xs],
  pathVars = [0..length xs - 1],
  poly     = constant (Dy (2^(length xs), 0)) * (p*p'),
  outVals  = Map.fromList $ [(xs!!i, ofVar (pathVar i)) | i <- [0..length xs - 1]]
  }
  where toFrac xs = foldMap (\(i, x) -> ofTerm (dyadic 1 i) [x]) (zip [1..] xs)
        p         = toFrac xs
        p'        = toFrac $ map pathVar [length xs-1,length xs-2..0]

verifyQFTN n () = do
  putStrLn $ "Verifying QFT, N=" ++ show n
  printVerStats (qft inputs)
  case verifySpec (qftSpec inputs) inputs inputs (qft inputs) of
    Nothing -> putStrLn $ "  Success!"
    Just _  -> putStrLn $ "  ERROR: failed to verify"
  where inputs = take n $ map (\i -> [i]) ['a'..]

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
  [S t, H t, CNOT t c1, T t, Tinv c1, CNOT t c1, CNOT c2 t,
   CNOT t c1, T c1, Tinv t, CNOT t c1, CNOT c2 t, H t, Sinv t]
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
generalProductGate (c:cs) t =
  [H t] ++ tmp ++ generalProductGate cs t ++ dagger tmp ++ dagger (generalProductGate cs t) ++ [H t]
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
omegaHack x = [T x, X x, T x, X x]

c1 x = concat $ replicate 8 (omegaHack x)
  
c2 x = [H x, H x]
c3 x = [S x, S x, S x, S x]
c4 x = [S x, H x, S x, H x, S x, H x] ++ dagger (omegaHack x)

c5  x y = cz x y ++ cz x y
c6  x y = [S x] ++ cz x y ++ [Sinv x] ++ cz x y
c7  x y = [S y] ++ cz x y ++ [Sinv y] ++ cz x y
c8  x y = [H x, S x, S x, H x] ++ cz x y ++ [H x, Sinv x, Sinv x, Sinv y, H x, Sinv y] ++ cz x y
c9  x y = [H y, S y, S y, H y] ++ cz x y ++ [H y, Sinv y, Sinv y, Sinv x, H y, Sinv x] ++ cz x y
c10 x y = cz x y ++ [H x] ++ cz x y ++ omegaHack x ++ [Sinv x, H x, Sinv x, Sinv y] ++ cz x y ++ [H x, Sinv x]
c11 x y = cz x y ++ [H y] ++ cz x y ++ omegaHack x ++ [Sinv y, H y, Sinv y, Sinv x] ++ cz x y ++ [H y, Sinv y]

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
        f (name, c) = case validate ["x", "y", "z"] ["x", "y", "z"] c [] of
          Nothing -> putStrLn $ "Successfully verified relation " ++ name
          _       -> putStrLn $ "ERROR: Failed to verify relation " ++ name
        mapSnds f xs    = map (mapSnd f) xs
        mapSnd f (a, b) = (a, f b)

{- Clifford+T identities -}

-- Defined gates
tx x = [H x, T x, H x]
ty x = [S x] ++ tx x ++ [Sinv x]

t1 x = concat $ replicate 8 (omegaHack x)

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
        f (name, c) = case validate ["x", "y"] ["x", "y"] c [] of
          Nothing -> putStrLn $ "Successfully verified relation " ++ name
          _       -> putStrLn $ "ERROR: Failed to verify relation " ++ name
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
      Rz m x   -> (Set.singleton x, 0, 0, 0)
    g (uids1, m1, c1, t1) (uids2, m2, c2, t2) =
      (Set.union uids1 uids2, m1+m2, c1+c2, t1+t2)
