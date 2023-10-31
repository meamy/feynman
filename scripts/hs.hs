{-# LANGUAGE BangPatterns #-}
{-|
Module      : Main
Description : Hidden shift
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Maybe

import Control.Monad

import Test.QuickCheck

import System.IO
import System.Environment               (getArgs)
import System.CPUTime                   (getCPUTime)

import Feynman.Core hiding              (getArgs)
import Feynman.Algebra.Linear hiding    (identity)
import qualified Feynman.Core as Core
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Verification.Symbolic

{- Hidden shift algorithm -}

genMCZ :: [String] -> Gen [Primitive]
genMCZ xs = do
  l   <- chooseInt (1, length xs)
  xs' <- shuffle xs
  return $ [Uninterp "MCZ" $ take l xs']

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

genSwap :: [String] -> Gen [Primitive]
genSwap xs = do
  x <- elements xs
  y <- elements $ xs \\ [x]
  return $ [Swap x y]

genPerm :: [String] -> Int -> Gen [Primitive]
genPerm xs bound = do
  l     <- chooseInt (0, bound)
  swaps <- replicateM l $ genSwap xs
  return $ concat swaps

genMaioranaGDeg3 :: [String] -> Int -> Int -> Gen [Primitive]
genMaioranaGDeg3 xs f 0 = return []
genMaioranaGDeg3 xs f i = do
  ccz   <- genCCZ xs
  cliff <- replicateM f $ oneof [genCZ xs, genZ xs]
  next  <- genMaioranaGDeg3 xs f (i-1)
  return $ concat (ccz:cliff) ++ next

genMaioranaG :: [String] -> Int -> Int -> Gen [Primitive]
genMaioranaG xs f 0 = return []
genMaioranaG xs f i = do
  mcz   <- genMCZ xs
  cliff <- replicateM f $ oneof [genCZ xs, genZ xs]
  next  <- genMaioranaG xs f (i-1)
  return $ concat (mcz:cliff) ++ next

hiddenShiftBG :: Int -> Int -> Int -> Gen ([Primitive], [String])
hiddenShiftBG n freq alternations = do
  s <- sublistOf vars
  g <- genMaioranaGDeg3 (take n2 vars) freq alternations
  let hTrans = map H vars
      xTrans = map X s 
      cTrans = [CZ (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      f' = (Core.subst (\i -> Map.findWithDefault i i sub) g) ++ cTrans
      f  = xTrans ++ g ++ cTrans ++ xTrans
  return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

hiddenShiftDeg3 :: Int -> Int -> Int -> Gen ([Primitive], [String])
hiddenShiftDeg3 n freq alternations = do
  s <- sublistOf vars
  g <- genMaioranaGDeg3 (take n2 vars) freq alternations
  p <- genPerm (take n2 vars) n
  let hTrans = map H vars
      xTrans = map X s 
      cTrans = [CZ (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub    = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      gAtY   = Core.subst (\i -> Map.findWithDefault i i sub) g
      pAtY   = Core.subst (\i -> Map.findWithDefault i i sub) p
      f' = gAtY ++ (Core.dagger pAtY) ++ cTrans ++ pAtY
      f  = xTrans ++ p ++ g ++ cTrans ++ (Core.dagger p) ++ xTrans
  return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

hiddenShift :: Int -> Int -> Int -> Gen ([Primitive], [String])
hiddenShift n freq alternations = do
  s <- sublistOf vars
  g <- genMaioranaG (take n2 vars) freq alternations
  p <- genPerm (take n2 vars) n
  let hTrans = map H vars
      xTrans = map X s 
      cTrans = [CZ (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
      sub    = Map.fromList $ zip (take n2 vars) (drop n2 vars)
      gAtY   = Core.subst (\i -> Map.findWithDefault i i sub) g
      pAtY   = Core.subst (\i -> Map.findWithDefault i i sub) p
      f' = gAtY ++ (Core.dagger pAtY) ++ cTrans ++ pAtY
      f  = p ++ g ++ cTrans ++ (Core.dagger p)
      --f  = xTrans ++ p ++ g ++ cTrans ++ (Core.dagger p) ++ xTrans
  return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
  where n2 = n `div` 2
        vars = ["x" ++ show i | i <- [0..n-1]]

simulateHiddenShift n c a () = do
  (circ, string) <- generate $ hiddenShiftBG n c a
  putStrLn $ "Simulating random Hidden Shift, n="
    ++ show n
    ++ ", Freq=" ++ show c
    ++ ", CCZ=" ++ show a
    ++ ", shift=" ++ show (fromBits . map (`elem` string) . reverse $ vars)
  putStrLn $ "Circuit length: " ++ show (length circ)
  start <- getCPUTime
  let !sop  = complexAction vars [] circ
  mid   <- getCPUTime
  let !sop' = simplify sop
  end   <- getCPUTime
  let t1 = (fromIntegral $ mid - start) / 10^9
  let t2 = (fromIntegral $ end - mid) / 10^9
  putStrLn $ "Generation time: " ++ show t1
  putStrLn $ "Simplification time: " ++ show t2
  putStrLn $ "Final state: " ++ show sop'
  where vars = ["x" ++ show i | i <- [0..n-1]]

-- | Main script

go :: [String] -> IO ()
go [n,f,a] = simulateHiddenShift (read n) (read f) (read a) ()

main :: IO ()
main = hSetEncoding stdout utf8 >> getArgs >>= go
