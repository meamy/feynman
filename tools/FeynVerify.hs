{-# LANGUAGE TupleSections #-}
module Main (main) where

import Feynman.Core (Primitive(CNOT, T, Tinv), ID)
import Feynman.Frontend.DotQC
import Feynman.Verification.SOP

import System.Environment
import System.Time
import Numeric

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Control.DeepSeq

data Result = Eq | NEq

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

equivalenceCheck src src' = do
  qc  <- parseDotQC src
  qc' <- parseDotQC src'
  return $ ver qc qc'
  where ver qc qc' =
          let gates  = toCliffordT . toGatelist $ qc
              gates' = toCliffordT . toGatelist $ qc'
              ins    = Set.toList $ inputs qc
              result = validate (union (qubits qc) (qubits qc')) ins gates gates'
          in
            case (inputs qc == inputs qc', result) of
              (False, _)  -> NEq
              (_, Just _) -> NEq
              _           -> Eq

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "Feynver -- quantum circuit equivalence checker",
          "Written by Matthew Amy",
          "",
          "Usage: feynver <circuit1>.qc <circuit2>.qc",
          ""
          ]

run :: [String] -> IO ()
run (x:y:[])
  | (drop (length x - 3) x == ".qc") && (drop (length y - 3) y == ".qc") = do
      xsrc <- readFile x
      ysrc <- readFile y
      TOD starts startp <- getClockTime
      let result        = equivalenceCheck xsrc ysrc
      TOD ends endp     <- result `seq` getClockTime
      let time = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
      case result of
        Left l      -> putStrLn $ show l
        Right (Eq)  -> putStrLn $ "Equal (" ++ formatFloatN time 3 ++ "ms)"
        Right (NEq) -> putStrLn $ "Not equal (" ++ formatFloatN time 3 ++ "ms)"
run _ = do
      putStrLn "Invalid argument(s)"
      printHelp

main :: IO ()
main = getArgs >>= run
