{-# LANGUAGE TupleSections #-}
module Main (main) where

import Control.Monad.Trans.Class  (lift)
import Control.Monad.Trans.Except (ExceptT(..), runExceptT, except)
import System.Environment         (getArgs)
import System.CPUTime             (getCPUTime)
import Data.List                  (takeWhile, union, (\\))
import Data.Set                   (Set)
import Text.Printf                (printf)
import Text.Parsec                (ParseError)

import qualified Data.ByteString as B
import qualified Data.Set as Set

import Feynman.Core hiding (inputs, qubits, getArgs)
import Feynman.Frontend.DotQC
import Feynman.Algebra.Base (FF2,DMod2)
import Feynman.Algebra.Pathsum.Balanced (Pathsum, grind, (.>), ssimulate)
import qualified Feynman.Algebra.Pathsum.Balanced as B
import Feynman.Verification.Symbolic

-- | Get the (reduced) path sum of a DotQC circuit
getSOP :: DotQC -> Pathsum DMod2
getSOP qc = B.simplify $ sopOfCircuit vars inpts circ where
  vars  = qubits qc
  inpts = Set.toList (inputs qc)
  circ  = toCliffordT $ toGatelist qc

-- | Get the extension of a filename
extension :: String -> String
extension = reverse . takeWhile (/= '.') . reverse

-- | Print the menu
printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "FeynSim -- quantum circuit simulator",
          "Written by Matthew Amy",
          "",
          "Given bit strings x=x1...xn and y=y1...yn, calculates the",
          "amplitude <y|U|x> of the given circuit U",
          "",
          "Usage: feynsim <x1...xn> <y1...yn> <circuit>.qc",
          ""
          ]

-- | Time a computation
withTiming :: (a -> b) -> a -> IO (b, Double)
withTiming f a = do
  start <- getCPUTime
  let res = f a
  res `seq` return ()
  end   <- getCPUTime
  return (res, (fromIntegral $ end - start) / 10^12)

-- | Print an Either
printError :: Either ParseError String -> IO ()
printError (Left err) = print err
printError (Right st) = putStrLn st

-- | Parses a bit string
parseBitstring :: String -> [FF2]
parseBitstring []  = []
parseBitstring "e" = []
parseBitstring (x:xs) = case x of
  '0' -> 0:(parseBitstring xs)
  '1' -> 1:(parseBitstring xs)
  _   -> error $ "Invalid character \"" ++ [x] ++ "\""

-- | Main program
run :: Set String -> [String] -> ExceptT ParseError IO String
run options xs = case xs of
  [x,y,z] | extension z == "qc" -> do
              zsrc <- lift $ B.readFile z
              qc   <- ExceptT $ return $ parseDotQC zsrc
              let xstr = parseBitstring x
              let ystr = parseBitstring y
              return . show $ ssimulate ystr (getSOP qc) xstr
  _ -> do
    lift $ putStrLn "Invalid argument(s)"
    lift $ printHelp
    return ""

main :: IO ()
main = do
  args   <- getArgs
  result <- runExceptT $ run Set.empty args
  printError result
