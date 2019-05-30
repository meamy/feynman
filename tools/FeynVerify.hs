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

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

equivalenceCheck src src' = do
  qc  <- parseDotQC src
  qc' <- parseDotQC src'
  return $ ver qc qc'
  where ver qc qc' =
          let gates  = toCliffordT . toGatelist $ qc
              gates' = toCliffordT . toGatelist $ qc'
              ins    = Set.toList $ inputs qc
          in
            if inputs qc /= inputs qc'
            then NotIdentity "Inputs don't match"
            else validate (union (qubits qc) (qubits qc')) ins gates gates'

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

printResult result time = case result of
  Identity pf -> do
    putStrLn $ "Equal (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Proof:"
    mapM_ (\rl -> putStrLn $ "  " ++  show rl) pf
  NotIdentity ce -> do
    putStrLn $ "Not equal (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Reason:"
    putStrLn $ "  " ++ ce
  Unknown sop -> do
    putStrLn $ "Inconclusive (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Residual path sum:"
    putStrLn $ "  " ++ show sop

run :: [String] -> IO ()
run (x:y:[])
  | (drop (length x - 3) x == ".qc") && (drop (length y - 3) y == ".qc") = do
      xsrc <- B.readFile x
      ysrc <- B.readFile y
      TOD starts startp <- getClockTime
      let result        = equivalenceCheck xsrc ysrc
      TOD ends endp     <- result `seq` getClockTime
      let time = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
      case result of
        Left l         -> putStrLn $ show l
        Right (result) -> printResult result time
run _ = do
      putStrLn "Invalid argument(s)"
      printHelp

main :: IO ()
main = getArgs >>= run
