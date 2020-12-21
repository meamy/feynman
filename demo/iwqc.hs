module Main where

import Data.List                        (find, splitAt)
import Data.Maybe                       (fromMaybe)
import qualified Data.Map as Map
import Control.Monad.State              (evalState, execState)
import Data.Semigroup                   ((<>))

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

actionST :: [Primitive] -> ID -> Pathsum DMod2
actionST circ t = grind $ inp .> conj .> action .> conj where
  action = dropPhase . grind $ evalState (computeAction circ) ctx
  inp    = (identity (inDeg action - 1)) <> (fresh .> xgate)
  conj   = (identity (inDeg action - 1)) <> hgate
  ctx    = Map.fromList [("a", 0), ("b", 1), ("c", 2), ("d", 3), ("e", 4)]

classifyST :: [Primitive] -> ID -> PhasePolynomial Var DMod2
classifyST circ t = fourier . phasePoly $ actionST circ t 

-- | Toffolis

toff x y z =
  [Tinv x, Tinv y, CNOT x y, T y, CNOT x y,
   H z, Tinv z, CNOT y z, T z, CNOT x z, Tinv z, CNOT y z, T z, CNOT x z, H z]

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

dirtyX' :: [ID] -> ID -> ID -> [Primitive]
dirtyX' xs t y = [H t] ++ go xs t y ++ [H t] where
  go [] t _       = [Z t]
  go (x:[]) t _   = [Sinv t, CNOT x t, S t, CNOT x t]
  go (x:y:[]) t _ = [Tinv t, CNOT x t, T t, CNOT y t, Tinv t, CNOT x t, T t, CNOT y t]
  go (x:y:xs) t z = rToffoli x t z ++
                    [H z] ++
                    dirtyXBullet' (y:xs) z x ++
                    [H z] ++
                    (dagger $ rToffoli x t z) ++
                    [H z] ++
                    (dagger $ dirtyXBullet' (y:xs) z x) ++
                    [H z]

dirtyX'' :: [ID] -> ID -> ID -> [Primitive]
dirtyX'' [] t y  = []
dirtyX'' [x] t y = [CNOT x t]
dirtyX'' xs t y  = go xs t y where -- ++ go (tail xs) y (head xs)  where
  go [] t _       = []
  go (x:[]) t _   = []
  go (x:y:[]) t _ = toff x y t
  go (x:xs) t y   = toff x y t ++ go xs y x ++ toff x y t

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

controlledXBullet' []     t = []
controlledXBullet' (c:[]) t = [CNOT c t]
controlledXBullet' cs     t =
  [H t, Tinv t] ++
  controlledXStar' cs' t ++
  [T t] ++
  controlledXStar' cs'' t ++
  [Tinv t] ++
  dagger (controlledXStar' cs' t) ++
  [T t] ++
  dagger (controlledXStar' cs'' t) ++
  [H t]
  where (xs, ys) = splitAt (((length cs) - 2) `div` 2) (drop 2 cs)
        cs'      = [cs!!0] ++ xs
        cs''     = [cs!!1] ++ ys

-- | Single-target gates

class0000 = []
class8000 = controllediX ["a", "b", "c", "d"] "e"
class8080 = controllediX ["a", "b", "c"] "e"
class0888 = controllediX ["a", "b", "c", "d"] "e" ++ controllediX ["a", "b"] "e"
class8888 = controllediX ["a", "b"] "e"
class7080 = controllediX ["a", "b", "c"] "e" ++  controllediX ["c", "d"] "e"
class7880 = [X "c", X "d"] ++ controllediX ["a", "b", "c", "d"] "e" ++ [X "c", X "d"] ++
            controllediX ["a", "b"] "e" ++  controllediX ["c", "d"] "e"
class7888 = controllediX ["a", "b"] "e" ++ controllediX ["c", "d"] "e"

minimalProductGate []     t = []
minimalProductGate (c:[]) t = [CNOT c t]
minimalProductGate (c:cs) t = tmp ++ minimalProductGate cs t ++ dagger tmp
  where tmp = [H t, Tinv t, CNOT c t, T t, CNOT c t] 

minimalProductGate' []            t = []
minimalProductGate' (c:[])        t = [CNOT c t]
minimalProductGate' (c:cs)    t = tmp ++ minimalProductGate' cs t ++ dagger tmp
  where tmp = [S t, H t, Tinv t, CNOT c t, T t, CNOT c t] 

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

genCXBullet' :: Integer -> [Primitive]
genCXBullet' k = controlledXBullet' (genList k) ("x" ++ subscript k)

genMPG :: Integer -> [Primitive]
genMPG k = minimalProductGate (genList k) ("x" ++ subscript k)

genMPG' :: Integer -> [Primitive]
genMPG' k = minimalProductGate' (genList k) ("x" ++ subscript k)


-- | Temporary
cxiAction :: Integer -> Pathsum DMod2
cxiAction k = grind $ (tensor (identity $ fromInteger k) $ initialize 0) .> sop where
  sop    = evalState (computeAction $ genCiX k ++ [Sinv ("x" ++ subscript k)]) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

cxstarAction :: Integer -> Pathsum DMod2
cxstarAction k = grind $ (tensor (identity $ fromInteger k) $ initialize 0) .> sop where
  sop    = evalState (computeAction $ genCXStar' k ++ [Sinv ("x" ++ subscript k)]) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

cxbulletAction :: Integer -> Pathsum DMod2
cxbulletAction k = grind $ (tensor (identity $ fromInteger k) $ initialize 0) .> sop where
  sop    = evalState (computeAction $ genCXBullet' k ++ [Sinv ("x" ++ subscript k)]) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

cxbulletDirtyAction :: Integer -> Pathsum DMod2
cxbulletDirtyAction k = grind sop where
  circ   = dirtyXBullet' ["x" ++ subscript i | i <- [1..k-1]] ("x" ++ subscript k) ("x" ++ subscript 0)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

cxDirtyAction :: Integer -> Pathsum DMod2
cxDirtyAction k = grind sop where
  circ   = dirtyX' ["x" ++ subscript i | i <- [1..k-1]] ("x" ++ subscript k) ("x" ++ subscript 0)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

pinvAction :: Integer -> Pathsum DMod2
pinvAction k = grind sop where
  targ   = "x" ++ subscript 0
  anc    = "x" ++ subscript 1
  circ   = [H targ] ++
           dagger (dirtyXBullet' ["x" ++ subscript i | i <- [2..k-1]] targ anc) ++
           [H targ]
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k]) [0..]

cxstarinvAction :: Integer -> Pathsum DMod2
cxstarinvAction k = grind sop where
  targ  = "x" ++ subscript k
  targ' = "x" ++ subscript 0
  danc  = "x" ++ subscript 1
  xs    = ["x" ++ subscript i | i <- [2..k-1]]
  anc   = "anc"
  circ = [H targ] ++
         rToffoli4 targ danc targ' anc ++
         [CNOT targ' anc] ++
         [H anc] ++
         dagger (dirtyXBullet' xs anc danc) ++
         [H anc] ++
         [CNOT targ' anc] ++
         dagger (rToffoli4 targ danc targ' anc)
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k, "anc"]) [0..]
  sop    = tensor (identity (fromInteger $ k+1)) (initialize 0) .> (evalState (computeAction circ) istate)

cxbulletinvAction :: Integer -> Pathsum DMod2
cxbulletinvAction k = grind sop where
  targ  = "x" ++ subscript k
  targ' = "x" ++ subscript 0
  danc  = "x" ++ subscript 1
  xs    = ["x" ++ subscript i | i <- [2..k-1]]
  anc   = "anc"
  circ = [H targ] ++
         rToffoli4 targ danc targ' anc ++
         [CNOT danc anc] ++
         [CNOT targ' anc] ++
         [H anc] ++
         dagger (dirtyX' xs anc danc) ++
         [H anc] ++
         [CNOT targ' anc] ++
         [CNOT danc anc] ++
         dagger (rToffoli4 targ danc targ' anc)
  istate = Map.fromList $ zip (reverse (genList k) ++ ["x" ++ subscript k, "anc"]) [0..]
  sop    = tensor (identity (fromInteger $ k+1)) (initialize 0) .> (evalState (computeAction circ) istate)
