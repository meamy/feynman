{-|
Module      : Main
Description : Circuit
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.List                               (splitAt)
import qualified Data.Map as Map
import Control.Monad.State.Strict              (evalState)
import Data.Semigroup                          ((<>))
import Text.Printf

import Feynman.Core                            (ID, Primitive(..), dagger)
import Feynman.Util.Unicode                    (subscript, ulambda, bullet, star)
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial              (degree)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)
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
  action = grind $ evalState (computeAction circ) ctx
  inp    = (identity (inDeg action - 1)) <> (fresh .> xgate)
  conj   = (identity (inDeg action - 1)) <> hgate
  ctx    = Map.fromList [("a", 0), ("b", 1), ("c", 2), ("d", 3), ("e", 4)]

classifyST :: [Primitive] -> ID -> PhasePolynomial Var DMod2
classifyST circ t = fourier . phasePoly $ actionST circ t 

-- | Toffoli gates

-- controlled S dagger
cS :: ID -> ID -> [Primitive]
cS x y = [T x, T y, CNOT x y, Tinv y, CNOT x y]

-- Toffoli gate
ccX :: ID -> ID -> ID -> [Primitive]
ccX x y z =
  [Tinv x, Tinv y, CNOT x y, T y, CNOT x y,
   H z, Tinv z, CNOT y z, T z, CNOT x z, Tinv z, CNOT y z, T z, CNOT x z, H z]

-- cciX
cciX :: ID -> ID -> ID -> [Primitive]
cciX x y z =
  [H z, Tinv z, CNOT y z, T z, CNOT x z, Tinv z, CNOT y z, T z, CNOT x z, H z]

-- Maslov's relative phase Toffoli-4
cccXStar :: ID -> ID -> ID -> ID -> [Primitive]
cccXStar w x y z =
  [H z, T z, CNOT y z, Tinv z, H z] ++
  [CNOT w z, T z, CNOT x z, Tinv z, CNOT w z, T z, CNOT x z, Tinv z] ++ 
  [H z, T z, CNOT y z, Tinv z, H z]

-- T-count 8(k-2) + 4 relative phase Toffoli with 1 dirty ancilla
dirtyXBullet :: [ID] -> ID -> ID -> [Primitive]
dirtyXBullet xs t y = [H t] ++ go xs t y ++ [H t] where
  go [] t _       = [Z t]
  go (x:[]) t _   = [H t, CNOT x t, H t]
  go (x:y:[]) t _ = [H t] ++ cciX x y t ++ [H t]
  go (x:xs) t a   = cciX x t a ++ go xs a x ++ dagger (cciX x t a)

-- T-count 16(k-2) Toffoli with 1 dirty ancilla
dirtyX :: [ID] -> ID -> ID -> [Primitive]
dirtyX xs t y = go xs t y where
  go [] t _       = [X t]
  go (x:[]) t _   = [CNOT x y]
  go (x:y:[]) t _ = ccX x y t
  go (x:xs) t a   = dirtyXBullet (x:xs) t a ++ [H a] ++ dagger (dirtyXBullet xs a x) ++ [H a]

-- T-count 16(k-3) + 4 multiply controlled iX gate
controllediX :: [ID] -> ID -> [Primitive]
controllediX []     t = []
controllediX (x:[]) t = [CNOT x t]
controllediX xs     t =
  [H t, Tinv t] ++
  dirtyXBullet xs' t a1 ++
  [T t] ++
  dirtyXBullet xs'' t a2 ++
  [Tinv t] ++
  dagger (dirtyXBullet xs' t a1) ++
  [T t] ++
  dagger (dirtyXBullet xs'' t a2) ++
  [H t]
  where (xs', xs'') = splitAt (length xs `div` 2) xs
        a1          = if null xs'' then "" else head xs''
        a2          = if null xs' then "" else head xs'

-- T-count 8(k-2) relative phase Toffoli gate
controlledX []     t = []
controlledX (x:[]) t = [CNOT x t]
controlledX (x:y:[]) t = ccX x y t
controlledX (x:y:xs) t = ccX x y t ++ dirtyXBullet xs y x ++ ccX x y t ++ dagger (dirtyXBullet xs y x)

-- T-count 8(k-2) relative phase Toffoli gate
controlledXStar []     t = []
controlledXStar (x:[]) t = [CNOT x t]
controlledXStar (x:xs) t = conj ++ dirtyXBullet xs t x ++ dagger conj
  where conj = [H t, T t, CNOT x t, Tinv t]

-- T-count 16(k-4) + 4 relative phase Toffoli gate
controlledXBullet []     t = []
controlledXBullet (x:[]) t = [CNOT x t]
controlledXBullet xs     t =
  [H t, Tinv t] ++
  controlledXStar xs' t ++
  [T t] ++
  controlledXStar xs'' t ++
  [Tinv t] ++
  dagger (controlledXStar xs' t) ++
  [T t] ++
  dagger (controlledXStar xs'' t) ++
  [H t]
  where (xs', xs'') = splitAt (length xs `div` 2) xs

-- | Single-target gates

-- T-count 4(k-1) degree k single target gate
controlledfk :: [ID] -> ID -> [Primitive]
controlledfk [] t     = []
controlledfk (x:[]) t = [CNOT x t]
controlledfk (c:xs) t = conj ++ controlledfk xs t ++ dagger conj
  where conj = [H t, Tinv t, CNOT c t, T t, CNOT c t] 

-- Alternate T-count 4(k-1) degree k single target gate
controlledfk' :: [ID] -> ID -> [Primitive]
controlledfk' [] t     = []
controlledfk' (x:[]) t = [CNOT x t]
controlledfk' (c:xs) t = conj ++ controlledfk' xs t ++ dagger conj
  where conj = [S t, H t, Tinv t, CNOT c t, T t, CNOT c t]

-- | Verification
checkControlledXStar :: Integer -> Pathsum DMod2
checkControlledXStar k = grind sop where
  circ   = controlledXStar ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k]] [0..]

-- Check correctness of dirty X Bullet, up to relative phase
verifyDirtyXBullet :: Integer -> Bool
verifyDirtyXBullet k = dropPhase (grind sop) == mctgate (fromInteger k) <> identity 1 where
  circ   = dirtyXBullet ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k) ("x" ++ subscript (k+1))
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k+1]] [0..]

-- Check correctness of dirty X exactly
verifyDirtyX :: Integer -> Bool
verifyDirtyX k = grind sop == mctgate (fromInteger k) <> identity 1 where
  circ   = dirtyX ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k) ("x" ++ subscript (k+1))
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k+1]] [0..]

-- Check correctness of controlled iX, up to relative phase
verifyControllediX :: Integer -> Bool
verifyControllediX k = dropPhase (grind sop) == mctgate (fromInteger k) where
  circ   = controllediX ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k]] [0..]

-- Check correctness of controlled X Star, up to relative phase
verifyControlledXStar :: Integer -> Bool
verifyControlledXStar k = dropPhase (grind sop) == mctgate (fromInteger k) where
  circ   = controlledXStar ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k]] [0..]

-- Check correctness of controlled X Bullet, up to relative phase
verifyControlledXBullet :: Integer -> Bool
verifyControlledXBullet k = dropPhase (grind sop) == mctgate (fromInteger k) where
  circ   = controlledXBullet ["x" ++ subscript i | i <- [0..k-1]] ("x" ++ subscript k)
  sop    = evalState (computeAction $ circ) istate
  istate = Map.fromList $ zip ["x" ++ subscript i | i <- [0..k]] [0..]

-- Check that, up to phase, the controlled-fk gate implements a single-target gate
-- where the control is a degree k function
verifyControlledfk :: Int -> Bool
verifyControlledfk k = degree f == k && discard k sop == identity k where
  circ   = controlledfk ["x" ++ subscript (toInteger i) | i <- [0..k-1]] ("x" ++ subscript (toInteger k))
  sop    = dropPhase . grind $ evalState (computeAction $ circ) istate
  f      = (outVals sop)!!k
  istate = Map.fromList $ zip ["x" ++ subscript (toInteger i) | i <- [0..k]] [0..]

-- | Logical product creation/destruction

-- Logical product of 3 bits with T-count 8
and3 :: Pathsum DMod2
and3 = fresh <> identity 3 .>
       evalState (computeAction $ cccXStar "a" "b" "c" "d") ctx .>
       sdggate <> identity 3
  where ctx = Map.fromList [("d",0),("a",1),("b",2),("c",3)]

-- 3 bit product destructor with T-count 3 or 4
unand3 :: Pathsum DMod2
unand3 = channelize (hgate <> identity 3) .>
         embed measure 6 (*4) (*4) .>
         channelize (xgate <> identity 3) .>
         channelize ((controlled (simpleAction $ dagger $ cS "x" "y")) <> identity 1) .>
         channelize (xgate <> identity 3) .>
         channelize (controlled (grind $ simpleAction $ dagger $ [H "z"] ++ cciX "x" "y" "z" ++ [H "z"])) .>
         embed epsilon 6 (*4) (*4) -- trace out the measured qubit

-- Verify that and3 and unand3 are inverse channels
verify3and :: () -> Bool
verify3and _ = rho == grind (rho .> (channelize and3) .> unand3)
  where rho    = grind $ vectorize $ densify sstate
        sstate = open $ identity 3 -- symbolic state on 3 qubits

-- Logical product of k bits with T-count 16(k-3) + 4
andk :: Int -> Pathsum DMod2
andk k = fresh <> identity k .>
         evalState (computeAction $ controllediX ctrls tgt) ctx .>
         sdggate <> identity k
  where ctx   = Map.fromList $ zip (tgt:ctrls) [0..]
        ctrls = ["x" ++ show i | i <- [0..k-1]]
        tgt   = "x" ++ show k
  
-- k bit product destructor with T-count 0 or 16(k-4)
unandk :: Int -> Pathsum DMod2
unandk k = channelize (hgate <> fresh <> identity k) .>
           embed measure (2*(k+1)) (*(k+2)) (*(k+2)) .>
           channelize (controlled $ grind $ evalState (computeAction corr) ctx) .>
           embed epsilon (2*(k+1)) (*(k+2)) (*(k+2)) .> -- trace out the measured qubit
           channelize (unfresh <> identity k)
  where ctx   = Map.fromList $ zip (anc:ctrls ++ [x,y]) [0..]
        ctrls = ["x" ++ show i | i <- [0..k-3]]
        x     = "x" ++ show (k-2)
        y     = "x" ++ show (k-1)
        anc   = "y"
        corr  = cciX x y anc ++ [H anc] ++ dirtyX ctrls anc y ++ [H anc] ++ dagger (cciX x y anc)

-- Verify that andk and unandk are inverse channels
verifykand :: Int -> Bool
verifykand k = rho == grind (rho .> (channelize $ andk k) .> unandk k)
  where rho    = grind $ vectorize $ densify sstate
        sstate = open $ identity k -- symbolic state on k qubits

-- Logical product of k bits with T-count 8(k-2)
andkalt :: Int -> Pathsum DMod2
andkalt k = fresh <> identity k .>
         grind (evalState (computeAction $ controlledXStar ctrls tgt) ctx) .>
         sdggate <> identity k
  where ctx   = Map.fromList $ zip (tgt:ctrls) [0..]
        ctrls = ["x" ++ show i | i <- [0..k-1]]
        tgt   = "x" ++ show k

-- k bit product destructor with T-count 8(k-4) or 8(k-4) + 4
unandkaltu :: Int -> Pathsum DMod2
unandkaltu k = (hgate <> fresh <> identity k) .>
           (controlled . grind $ evalState (computeAction $ ccX x y anc) ctx) .>
           (grind $ identity 1 <> evalState (computeAction $ corr) ctx) .>
           (controlled . grind $ evalState (computeAction . dagger $ ccX x y anc) ctx)
  where ctx   = Map.fromList $ zip (anc:[y,x] ++ ctrls) [0..]
        ctrls = ["x" ++ show i | i <- [0..k-3]]
        x     = "x" ++ show (k-2)
        y     = "x" ++ show (k-1)
        anc   = "y"
        corr  = [CNOT y anc, H anc] ++ dagger (dirtyXBullet ctrls anc x) ++ [H anc, CNOT y anc]
  
-- k bit product destructor with T-count 8(k-4) or 8(k-4) + 4
unandkalt :: Int -> Pathsum DMod2
unandkalt k = channelize (hgate <> fresh <> identity k) .>
           embed measure (2*(k+1)) (*(k+2)) (*(k+2)) .>
           channelize (controlled . grind $ evalState (computeAction $ cciX x y anc) ctx) .>
           channelize (grind $ identity 1 <> evalState (computeAction $ corr) ctx) .>
           channelize (controlled . grind $ evalState (computeAction . dagger $ cciX x y anc) ctx) .>
           embed epsilon (2*(k+1)) (*(k+2)) (*(k+2)) .> -- trace out the measured qubit
           channelize (unfresh <> identity k)
  where ctx   = Map.fromList $ zip (anc:ctrls ++ [x,y]) [0..]
        ctrls = ["x" ++ show i | i <- [0..k-3]]
        x     = "x" ++ show (k-2)
        y     = "x" ++ show (k-1)
        anc   = "y"
        corr  = [CNOT y anc, H anc] ++ dagger (dirtyXBullet ctrls anc x) ++ [H anc, CNOT y anc]

-- Verify that andkalt and unandkalt are inverse channels
verifykandalt :: Int -> Bool
verifykandalt k = rho == grind (rho .> (channelize $ andkalt k) .> unandkalt k)
  where rho    = grind $ vectorize $ densify sstate
        sstate = open $ identity k -- symbolic state on k qubits

-- | Main script

main :: IO ()
main = do
  putStrLn "...I am a verification bot, beep boop..."
  putStrLn "...I will check some circuits for you..."
  putStrLn ""
  putStrLn "Construction 1: Relative phase Toffoli with 1 dirty ancilla"
  mapM_ checkdirtyXBullet [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn "Construction 2: Toffoli with 1 dirty ancilla"
  mapM_ checkdirtyX [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn "Construction 3: Multiply-controlled iX"
  mapM_ checkiX [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn $ "Construction 4: Multiply-controlled X" ++ star
  mapM_ checkXStar [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn $ "Construction 5: Multiply-controlled X" ++ bullet
  mapM_ checkXBullet [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn "Construction 6: Temporary logical 3-AND"
  mapM_ check3and [()]
  putStrLn ""
  putStrLn "Construction 7: Temporary logical k-AND"
  mapM_ checkkand [2^i | i <- [1..6]]
  putStrLn ""
  putStrLn $ "Construction 8: Temporary logical k-AND (with X" ++ star ++ ")"
  mapM_ checkkandalt [2^i | i <- [1..6]]
  where
  checkdirtyXBullet :: Integer -> IO ()
  checkdirtyXBullet k = do
    printf "    checking %s%s(X%s) (1 dirty ancilla) up to phase..." ulambda (subscript k) bullet
    printf "%s\n" (if verifyDirtyXBullet k then "Success!" else "Failed")
  checkdirtyX :: Integer -> IO ()
  checkdirtyX k = do
    printf "    checking %s%s(X) (1 dirty ancilla)..." ulambda (subscript k)
    printf "%s\n" (if verifyDirtyX k then "Success!" else "Failed")
  checkiX :: Integer -> IO ()
  checkiX k = do
    printf "    checking %s%s(iX) (ancilla-free)..." ulambda (subscript k)
    printf "%s\n" (if verifyControllediX k then "Success!" else "Failed")
  checkXStar :: Integer -> IO ()
  checkXStar k = do
    printf "    checking %s%s(X%s) (ancilla-free)..." ulambda (subscript k) star
    printf "%s\n" (if verifyControlledXStar k then "Success!" else "Failed")
  checkXBullet :: Integer -> IO ()
  checkXBullet k = do
    printf "    checking %s%s(X%s) (ancilla-free)..." ulambda (subscript k) bullet
    printf "%s\n" (if verifyControlledXBullet k then "Success!" else "Failed")
  check3and :: () -> IO ()
  check3and _ = do
    printf "    checking 3-AND and un-3-AND are inverse channels..."
    printf "%s\n" (if verify3and () then "Success!" else "Failed")
  checkkand :: Int -> IO ()
  checkkand k = do
    printf "    checking %i-AND and un-%i-AND are inverse channels..." k k
    printf "%s\n" (if verifykand k then "Success!" else "Failed")
  checkkandalt :: Int -> IO ()
  checkkandalt k = do
    printf "    checking %i-AND%s and un-%i-AND%s are inverse channels..." k star k star
    printf "%s\n" (if verifykandalt k then "Success!" else "Failed")
