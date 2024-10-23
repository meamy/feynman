{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
module Main (main) where

import Benchmarks
import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Either (isRight)
import Data.List
import Data.Map (Map, toList)
import qualified Data.Map as Map
import Data.Maybe (maybeToList)
import qualified Data.Set as Set
import Feynman.Core (Loc)
import qualified Feynman.Frontend.DotQC as DotQC
import Feynman.Frontend.Frontend
import Feynman.Frontend.OpenQASM.Driver
import qualified Feynman.Frontend.OpenQASM.Syntax as QASM2
import Feynman.Frontend.OpenQASM3.Driver
import qualified Feynman.Frontend.OpenQASM3.Semantics as QASM3
import System.Environment (getArgs)
import System.FilePath (takeExtension)
import System.IO (hPutStrLn, stderr)

{- Toolkit passes -}

data Options = Options
  { useQASM3 :: Bool
  }

statsJsonLines :: ProgramStats -> [String]
statsJsonLines stats =
  let bc = map (\x -> "  \"bits\": " ++ show x) (maybeToList . bitCount $ stats)
      qbc = ["  \"qubits\": " ++ (show . qubitCount $ stats)]
      gd = map (\x -> "  \"depth\": " ++ show x) (maybeToList . gateDepth $ stats)
      td = map (\x -> "  \"t_depth\": " ++ show x) (maybeToList . tDepth $ stats)
      counts = map (\(gate, count) -> "    \"" ++ gate ++ "\": " ++ show count) $ toList (gateCounts stats)
   in ["{", "  \"gates\": {"] ++ addSeps counts ++ ["  },"] ++ (addSeps $ concat [bc, qbc, gd, td]) ++ ["}"]
  where
    addSeps :: [String] -> [String]
    addSeps lines@[] = lines
    addSeps lines@[_] = lines
    addSeps (line : tail) = (line ++ ",") : (addSeps tail)

{- DotQC -}

runStats :: forall a. (ProgramRepresentation a) => (a -> ProgramStats) -> Options -> String -> IO ()
runStats statsFn options path = do
  parseResult <- readAndParse path
  case parseResult of
    Left err -> hPutStrLn stderr $ "ERROR: " ++ err
    Right qprog -> do
      mapM_ putStrLn $ statsJsonLines $ statsFn qprog

dotQCStats :: Options -> DotQC.DotQC -> ProgramStats
dotQCStats options = computeStats

qasmStats :: Options -> QASM2.QASM -> ProgramStats
qasmStats options = computeStats

qasm3Stats :: Options -> QASM3.SyntaxNode Loc -> ProgramStats
qasm3Stats options = computeStats

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where
    lines =
      [ "Feynman -- quantum circuit toolkit",
        "Written by Matthew Amy and Joseph Lunderville",
        "",
        "Run with feyncount [-qasm3] (<circuit>.(qc | qasm))",
        "",
        "Options:",
        "  -qasm3\tRun using the openQASM 3 frontend"
      ]

defaultOptions :: Options
defaultOptions =
  Options
    { useQASM3 = False
    }

parseArgs :: Bool -> Options -> [String] -> IO ()
parseArgs doneSwitches options [] = printHelp
parseArgs doneSwitches options (x : xs) = case x of
  f | doneSwitches -> runFile f
  "-h" -> printHelp
  "-qasm3" -> parseArgs doneSwitches options {useQASM3 = True} xs
  "--" -> parseArgs True options xs
  f | ((drop (length f - 3) f) == ".qc") || ((drop (length f - 5) f) == ".qasm") -> runFile f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where
    runFile f | (takeExtension f) == ".qc" = runStats (dotQCStats options) options f
    runFile f
      | (takeExtension f) == ".qasm" =
          if useQASM3 options
            then runStats (qasm3Stats options) options f
            else runStats (qasmStats options) options f
    runFile f = putStrLn ("Unrecognized file type \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs False defaultOptions
