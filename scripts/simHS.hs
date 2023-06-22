{-|
Module      : Main
Description : Script for simulating an instance of a hidden shift problem
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Main where

import System.Environment (getArgs)
import Feynman.Verification.SOP (simulateHiddenShift)

run :: [String] -> IO ()
run []    = putStrLn "Invalid arguments"
run [x,y] = simulateHiddenShift (read x) (read y) ()

main :: IO ()
main = getArgs >>= run
