module Main where

import Data.List                        (find, splitAt)
import Data.Maybe                       (fromMaybe)

import Feynman.Core                     (ID, Primitive(..), dagger)
import Feynman.Util.Unicode             (subscript)
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Verification.Symbolic 

-- | Utilities

genList :: Integer -> [String]
genList n = ["x" ++ subscript i | i <- [0..n-1]]

tCount :: [Primitive] -> Int
tCount = length . filter isT where
  isT (T _)    = True
  isT (Tinv _) = True
  isT _        = False

whSpectrum :: [Primitive] -> PhasePolynomial Var DMod2
whSpectrum = fourier . phasePoly . grind . simpleAction

-- | Circuits

rToffoli x y z =
  [H z, Tinv z, CNOT y z, T z, CNOT x z, Tinv z, CNOT y z, T z, CNOT x z, H z]

rToffoli4 w x y z =
  [H z, T z, CNOT y z, Tinv z, H z] ++
  [CNOT w z, T z, CNOT x z, Tinv z, CNOT w z, T z, CNOT x z, Tinv z] ++ 
  [H z, T z, CNOT y z, Tinv z, H z]

dirtyX :: [ID] -> ID -> [ID] -> [Primitive]
dirtyX xs t ys = [H t] ++ go xs t ys ++ [H t] where
  go [] t _            = [Z t]
  go (x:[]) t _        = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t _      = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t (z:ys) = rToffoli x t z ++ go (y:xs) z ys ++ (dagger $ rToffoli x t z)

dirtyXBullet :: [ID] -> ID -> [ID] -> [Primitive]
dirtyXBullet xs t ys = [H t] ++ go xs t ys ++ [H t] where
  go [] t _            = [Z t]
  go (x:[]) t _        = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t _      = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t (z:ys)
    | length xs >= 2 = rToffoli4 x y t z ++ go xs z ys ++ (dagger $ rToffoli4 x y t z)
    | otherwise      = rToffoli x t z ++ go (y:xs) z ys ++ (dagger $ rToffoli x t z)

dirtyXStar :: [ID] -> ID -> [ID] -> [Primitive]
dirtyXStar (x:xs) y ys
  | xs == []  = [H y, S y, CNOT x y, Sinv y, CNOT x y, H y]
  | otherwise = [H y, Tinv y, CNOT x y, T y] ++ dirtyXBullet xs y ys ++ [Tinv y, CNOT x y, T y, H y]

dirtyXBullet' :: [ID] -> ID -> ID -> [Primitive]
dirtyXBullet' xs t y = [H t] ++ go xs t y ++ [H t] where
  go [] t _       = [Z t]
  go (x:[]) t _   = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t _ = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t z = rToffoli x t z ++ go (y:xs) z x ++ (dagger $ rToffoli x t z)

dirtyXBullet'' :: [ID] -> ID -> [Primitive]
dirtyXBullet'' xs t = [H t] ++ go xs t ++ [H t] where
  go [] t       = [Z t]
  go (x:[]) t   = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t = rToffoli t x y ++ go (y:xs) x ++ (dagger $ rToffoli t x y)

controllediX []     t = []
controllediX (c:[]) t = [CNOT c t]
controllediX cs     t =
  [H t, Tinv t] ++
  dirtyX cs' t cs'' ++
  [T t] ++
  dirtyX cs'' t cs' ++
  [Tinv t] ++
  dagger (dirtyX cs' t cs'') ++
  [T t] ++
  dagger (dirtyX cs'' t cs') ++
  [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXBullet []     t = []
controlledXBullet (c:[]) t = [CNOT c t]
controlledXBullet cs     t =
  [H t, Tinv t] ++
  dirtyXStar cs' t cs'' ++
  [T t] ++
  dirtyXStar cs'' t cs' ++
  [Tinv t] ++
  dagger (dirtyXStar cs' t cs'') ++
  [T t] ++
  dagger (dirtyXStar cs'' t cs') ++
  [H t]
  where (cs', cs'') = splitAt (length cs `div` 2) cs

controlledXStar []     t = []
controlledXStar (c:[]) t = [CNOT c t]
controlledXStar cs     t =
  [H t, T t] ++
  dirtyXStar cs'' t cs' ++
  [Tinv t] ++
  dirtyXBullet cs' t cs'' ++
  [T t] ++
  dagger (dirtyXStar cs'' t cs') ++
  [Tinv t, H t]
  where (cs', cs'') = splitAt (bestSplit $ length cs) cs
        bestSplit k = fromMaybe k . find (f k) . reverse $ [0..k]
        f k i       = floor (fromIntegral i / 2.0) <= (k-i)

controlledXStar' []        t = []
controlledXStar' (c:[])    t = [CNOT c t]
controlledXStar' (c:cs) t =
  [H t, T t, CNOT c t, Tinv t] ++
  dirtyXBullet' cs t c ++
  [T t, CNOT c t, Tinv t, H t]

minimalProductGate []     t = []
minimalProductGate (c:[]) t = [CNOT c t]
minimalProductGate (c:cs) t = tmp ++ minimalProductGate cs t ++ dagger tmp
  where tmp = [H t, Tinv t, CNOT c t, T t, CNOT c t] 

minimalProductGate' []     t = []
minimalProductGate' (c:[]) t = [CNOT c t]
minimalProductGate' (c:cs) t = tmp ++ minimalProductGate' cs t ++ dagger tmp
  where tmp = [H t, Tinv t, CNOT c t, Tinv t, CNOT c t] 

-- | Uncomputation circuits

rToffoli4inv0 w x y z = cSInv w x where
  cSInv w x = [Tinv w, Tinv x, CNOT w x, T x, CNOT w x]

rToffoli4inv1 w x y z = ciZInv w x y where
  ciZInv w x y = [T y, CNOT w y, Tinv y, CNOT x y, T y, CNOT w y, Tinv y, CNOT x y]

-- | Convenience generators

genCiX :: Integer -> [Primitive]
genCiX k = controllediX (genList k) ("x" ++ subscript k)

genCXBullet :: Integer -> [Primitive]
genCXBullet k = controlledXBullet (genList k) ("x" ++ subscript k)

genCXStar :: Integer -> [Primitive]
genCXStar k = controlledXStar (genList k) ("x" ++ subscript k)

genCXStar' :: Integer -> [Primitive]
genCXStar' k = controlledXStar' (genList k) ("x" ++ subscript k)

genMPG :: Integer -> [Primitive]
genMPG k = minimalProductGate (genList k) ("x" ++ subscript k)

genMPG' :: Integer -> [Primitive]
genMPG' k = minimalProductGate' (genList k) ("x" ++ subscript k)
