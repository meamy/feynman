{-|
Module      : Main
Description : Pauli exponential experiments
Copyright   : (c) Matthew Amy, 2023
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import Data.List                               (splitAt,find,unfoldr)
import qualified Data.Map as Map
import Data.Semigroup                          ((<>))

import Control.Monad
import Control.Concurrent

import System.Environment

import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced

-- | Utilities

-- Thin a list to every `n`th element starting with index `i`
thin :: Int -> Int -> [a] -> [a]
thin i n = unfoldr step . drop i
  where step [] = Nothing
        step (y:ys) = Just (y, drop (n-1) ys)

-- Use `n` parallel threads to find first element of `xs` satisfying `f`
parFind :: Int -> (a -> Bool) -> [a] -> IO (Maybe a)
parFind n f xs = do
  resultV <- newEmptyMVar
  runningV <- newMVar n
  comparisonsV <- newMVar 0
  threads <- forM [0..n-1] $ \i -> forkIO $ do
    case find f (thin i n xs) of
      Just x -> void (tryPutMVar resultV (Just x))
      Nothing -> do m <- takeMVar runningV
                    if m == 1
                      then void (tryPutMVar resultV Nothing)
                      else putMVar runningV (m-1)
  result <- readMVar resultV
  mapM_ killThread threads
  return result
  
paulis :: [PauliGate]
paulis = [PauliI, PauliX, PauliZ, PauliXZ]

allNonzeroPaulis :: Int -> [Pauli]
allNonzeroPaulis n = map (\p -> (I0, p)) . filter (/= (replicate n PauliI)) $ go n where
  go 0 = [[]]
  go n = [p:pp | p <- paulis, pp <- go (n-1)]

allPauliExponentialStrings :: Int -> Int -> [[Pauli]]
allPauliExponentialStrings n = go where
  go 0 = [[]]
  go k = [p:pp | p <- allNonzeroPaulis n, pp <- go (k-1)]

checkPauli :: Pathsum DMod2 -> Bool
checkPauli sop =
  let n    = inDeg sop
      zero = replicate n 0
      hcon = foldr (<>) hgate (replicate (n-1) hgate)
      c0X  = Map.filter (/= 0) $ simulate sop zero
      c0Z  = Map.filter (/= 0) $ simulate (hcon .> sop .> hcon) zero
  in
    case (Map.size c0X, Map.size c0Z) of
      (1, 1) -> True
      _      -> False

checkClifford :: Pathsum DMod2 -> Bool
checkClifford sop =
  let n    = inDeg sop
      xgen = [applyX i (identity n) | i <- [0..n-1]]
      zgen = [applyZ i (identity n) | i <- [0..n-1]]
  in
    all checkPauli $ map (\p -> sop .> p .> dagger sop) (xgen ++ zgen)

findClifford :: Int -> Int -> Maybe ([Pauli])
findClifford n k =
  let toCheck        = allPauliExponentialStrings n k
      computePathsum = foldl (.>) (identity n) . map (pauliExp (dMod2 1 2))
  in
    find (checkClifford . computePathsum) toCheck

parFindClifford :: Int -> Int -> Int -> IO (Maybe [Pauli])
parFindClifford t n k =
  let toCheck        = allPauliExponentialStrings n k
      computePathsum = foldl (.>) (identity n) . map (pauliExp (dMod2 1 2))
  in
    parFind t (checkClifford . computePathsum) toCheck

-- | Main script

main :: IO ()
main = do
  [t, n, k] <- getArgs
  putStrLn $ "...I am your pauli exponential helper, beep boop..."
  putStrLn $ "...I will check if a " ++ n ++ " qubit string of " ++ k ++
             " pauli exponentials is clifford"
  ps <- parFindClifford (read t) (read n) (read k)
  case ps of
    Nothing    -> putStrLn "...Nope!"
    Just pauli -> putStrLn $ "...Found one: " ++ show pauli