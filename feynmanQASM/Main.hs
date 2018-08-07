{-# LANGUAGE TupleSections #-}
module Main (main) where

import Feynman.Core (Primitive(CNOT, T, Tinv), ID)
import Feynman.Frontend.OpenQASM.Lexer (lexer)
import Feynman.Frontend.OpenQASM.Syntax (QASM,
                                         prettyPrint,
                                         check,
                                         desugar,
                                         emit,
                                         fromDotQC,
                                         inline,
                                         applyOpt)
import Feynman.Frontend.OpenQASM.Parser (parse)
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.TPar
import Feynman.Verification.SOP

import System.Environment

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad
import System.Time
import Control.DeepSeq

{- Toolkit passes -}

type QASMPass = QASM -> Either String QASM

trivPass :: QASMPass
trivPass = Right

inlinePass :: QASMPass
inlinePass = Right . inline

optimizationPass :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> QASMPass
optimizationPass f qasm = Right $ applyOpt f qasm

phasefoldPass :: QASMPass
phasefoldPass = optimizationPass phaseFold

tparPass :: QASMPass
tparPass = optimizationPass tpar

cnotminPass :: QASMPass
cnotminPass = optimizationPass minCNOT

{- Main program -}

run :: QASMPass -> String -> String -> IO ()
run pass fname src = do
  case parseAndPass of
    Left err        -> putStrLn $ "ERROR: " ++ err
    Right (qasm, qasm') -> emit qasm'
  where printErr (Left l)  = Left $ show l
        printErr (Right r) = Right r
        parseAndPass = do
          let qasm   = parse . lexer $ src
          symtab <- check qasm
          qasm' <- pass $ desugar symtab qasm
          return (qasm, qasm')

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "Feynman -- quantum circuit toolkit",
          "Written by Matthew Amy",
          "",
          "Run with feyn [passes] (<circuit>.qasm)",
          "",
          "Passes:",
          "  -phasefold\tPhase folding pass, merges phase gates. Non-increasing in all metrics",
          "  -tpar\t\tPhase folding + T-parallelization algorithm from [AMM14]",
          "  -cnotmin\tPhase folding + CNOT-minimization algorithm from [AAM17]"
          ]
          

parseArgs :: QASMPass -> [String] -> IO ()
parseArgs pass []     = printHelp
parseArgs pass (x:xs) = case x of
  "-h"         -> printHelp
  "-inline"    -> parseArgs (pass >=> inlinePass) xs
  "-phasefold" -> parseArgs (pass >=> phasefoldPass) xs
  "-cnotmin"   -> parseArgs (pass >=> cnotminPass) xs
  "-tpar"      -> parseArgs (pass >=> tparPass) xs
  f | (drop (length f - 5) f) == ".qasm" -> readFile f >>= run pass f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs trivPass
