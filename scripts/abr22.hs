{-# LANGUAGE BangPatterns #-}
{-|
Module      : Main
Description : Extraction tests
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.Maybe                              (maybe, isJust)
import Control.Monad                           (sequence)
import Test.QuickCheck                         (Gen, generate, arbitrary)
import Text.Printf
import System.CPUTime                          (getCPUTime)

import Feynman.Core                            (ID, Primitive(..), dagger)
import Feynman.Util.Unicode                    (subscript, ulambda, bullet, star)
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial              (degree)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)
import Feynman.Synthesis.Pathsum.Clifford
import Feynman.Synthesis.Pathsum.Unitary

-- | Utilities
data Result = Result {
  success :: Bool,
  time    :: Double,
  before  :: Integer,
  after   :: Integer
  }

-- | Re-synthesizes a Clifford circuit and returns the results
synthesizeClifford :: [Primitive] -> IO Result
synthesizeClifford xs = do
  start <- getCPUTime
  let !count  = length xs
  let !xs'    = resynthesizeClifford xs
  let !count' = length xs'
  end   <- getCPUTime
  let t = (fromIntegral $ end - start) / 10^9
  return $ Result True t (fromIntegral count) (fromIntegral count')

-- | Re-synthesizes a Clifford+T circuit and returns the results
synthesizeCliffordT :: [Primitive] -> IO Result
synthesizeCliffordT xs = do
  start <- getCPUTime
  let !count  = length xs
  let !xs'    = resynthesizeCircuit xs
  let !count' = maybe 0 length xs'
  end   <- getCPUTime
  let t = (fromIntegral $ end - start) / 10^9
  return $ Result (isJust xs') t (fromIntegral count) (fromIntegral count')

-- | Generates random Clifford circuits, synthesizes them and prints statistics
cliffordTests :: Int -> Int -> Int -> IO ()
cliffordTests n k l = do
  circuits <- mapM (\_ -> generateClifford n k) [1..l]
  results  <- mapM synthesizeClifford circuits
  let avgT = foldr (+) 0 (map time results) / (fromIntegral l)
  let avgR = foldr (+) 0 (map reduction results) / (fromIntegral l)
  putStrLn $ "  avg time: " ++ (show avgT)
  putStrLn $ "  avg reduction: " ++ (show avgR)
  where reduction result =
          fromIntegral (before result - after result) / (fromIntegral $ before result) * 100
  
-- | Generates random Clifford+T circuits, synthesizes them and prints statistics
cliffordTTests :: Int -> Int -> Int -> IO ()
cliffordTTests n k l = do
  circuits <- mapM (\_ -> generateCliffordT n k) [1..l]
  results  <- mapM synthesizeCliffordT circuits
  let succ = filter success results
  let perc = (fromIntegral (length succ) / fromIntegral l) * 100
  let avgT = foldr (+) 0 (map time succ) / (fromIntegral $ length succ)
  let avgR = foldr (+) 0 (map reduction succ) / (fromIntegral $ length succ)
  putStrLn $ "  % successful: " ++ (show perc)
  putStrLn $ "  avg time: " ++ (show avgT)
  putStrLn $ "  avg reduction: " ++ (show avgR)
  where reduction result =
          fromIntegral (before result - after result) / (fromIntegral $ before result) * 100
  
-- | Main script
main :: IO ()
main = do
  putStrLn "...I am a synthesis bot, beep boop..."
  putStrLn "...I will synthesize some circuits for you..."
  putStrLn ""
  putStrLn "Clifford synthesis tests (1000 random circuits, 20 qubits, 300 gates)"
  cliffordTests 19 300 1000
  putStrLn "Clifford synthesis tests (1000 random circuits, 20 qubits, 500 gates)"
  cliffordTests 19 500 1000
  putStrLn "Clifford synthesis tests (1000 random circuits, 50 qubits, 300 gates)"
  cliffordTests 49 300 1000
  putStrLn "Clifford synthesis tests (1000 random circuits, 50 qubits, 500 gates)"
  cliffordTests 49 500 1000
