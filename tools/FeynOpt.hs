{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
module Main (main) where

import Feynman.Core (Primitive,
                     ID,
                     Loc,
                     simplifyPrimitive',
                     expandCNOT,
                     expandCNOT',
                     annotate,
                     unannotate,
                     expandCZ,
                     idsW)

import Feynman.Frontend.Frontend
import qualified Feynman.Frontend.DotQC as DotQC

import Feynman.Frontend.OpenQASM.Driver
import qualified Feynman.Frontend.OpenQASM.Syntax as QASM2
import qualified Feynman.Frontend.OpenQASM.Lexer  as QASM2Lexer
import qualified Feynman.Frontend.OpenQASM.Parser as QASM2Parser

import Feynman.Frontend.OpenQASM3.Driver
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import qualified Feynman.Frontend.OpenQASM3.Parser as QASM3Parser
import qualified Feynman.Frontend.OpenQASM3.Syntax as QASM3Syntax
import qualified Feynman.Frontend.OpenQASM3.Syntax.Transformations as QASM3
import qualified Feynman.Frontend.OpenQASM3.Semantics as QASM3

import Feynman.Optimization.PhaseFold
import Feynman.Optimization.StateFold
import Feynman.Optimization.TPar
import Feynman.Optimization.Clifford
import Feynman.Optimization.RelationalFold as L
import Feynman.Optimization.RelationalFoldNL as NL
import Feynman.Synthesis.Pathsum.Unitary hiding (MCT)
import Feynman.Verification.Symbolic

import System.Environment (getArgs)
import System.FilePath    (takeBaseName, takeDirectory, takeExtension)
import System.CPUTime     (getCPUTime)
import System.IO          (hPutStrLn, stderr)

import Control.Monad
import Control.DeepSeq (NFData, deepseq)

import Data.List
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Either (isRight)

import Benchmarks

{- Toolkit passes -}

data Options = Options
  { passes :: [Pass],
    verify :: Bool,
    pureCircuit :: Bool,
    useQASM3 :: Bool
  }

{- DotQC -}

runPasses :: forall a. (ProgramRepresentation a, NFData a) => [a -> a] -> Options -> String -> IO ()
runPasses passFns options path = do
  parseResult <- readAndParse path
  case parseResult of
    Left err -> hPutStrLn stderr $ "ERROR: " ++ err
    Right qprog -> do
      start <- qprog `deepseq` getCPUTime
      let qprog' = foldr ($) qprog passFns
      end <- qprog' `deepseq` getCPUTime
      let eqCheck = equivalenceCheck qprog qprog'
      let verified = verify options && isRight eqCheck
      when (verify options) . void $
        ( case equivalenceCheck qprog qprog' of
            Left err -> hPutStrLn stderr $ "ERROR: " ++ err
            Right qprog -> return ()
        )
      let time = (fromIntegral $ end - start) / 10 ^ 9
      let stats = computeStats qprog
      let stats' = computeStats qprog'
      let name = takeBaseName path
      putStr (prettyPrintWithBenchmarkInfo name time stats stats' verified qprog')

dotQCPasses :: Options -> [DotQC.DotQC -> DotQC.DotQC]
dotQCPasses options = map (applyPass True) (passes options)

qasmPasses :: Options -> [QASM2.QASM -> QASM2.QASM]
qasmPasses options = map (applyPass $ pureCircuit options) (passes options)

qasm3Passes :: Options -> [QASM3.SyntaxNode Loc -> QASM3.SyntaxNode Loc]
qasm3Passes options = map (applyPass $ pureCircuit options) (passes options)

{- Deprecated transformations for benchmark suites -}
benchPass :: (ProgramRepresentation a) => Options -> (a -> Either String a)
benchPass options = \qc -> Right $ foldr ($) qc (map (applyPass $ pureCircuit options) (passes options))

benchVerif :: Options -> Maybe (DotQC.DotQC -> DotQC.DotQC -> Either String DotQC.DotQC)
benchVerif options | verify options = Just equivalenceCheck
benchVerif options | not (verify options) = Nothing

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where
    lines =
      [ "Feynman -- quantum circuit toolkit",
        "Written by Matthew Amy",
        "",
        "Run with feynopt [passes] (<circuit>.(qc | qasm) | Small | Med | All | -benchmarks <path to folder>)",
        "",
        "Options:",
        "  -purecircuit\tPerform qasm passes assuming the initial state (of qubits) is unknown",
        "  -verify\tVerify equivalence of the output to the original circuit (only dotQC)",
        "  -qasm3\tRun using the openQASM 3 frontend",
        "",
        "Transformation passes:",
        "  -inline\tInline all sub-circuits",
        "  -unroll\tUnroll loops (QASM3 specific)",
        "  -mctExpand\tExpand all MCT gates using |0>-initialized ancillas",
        "  -toCliffordT\tExpand all gates to Clifford+T gates",
        "  -decompile\tDecompiles a Clifford+T circuit into multiply-controlled gates",
        "",
        "Optimization passes:",
        "  -simplify\tBasic gate-cancellation pass",
        "  -phasefold\tMerges phase gates according to the circuit's phase polynomial",
        "  -statefold <d>\tPhase folding with state invariants up to degree <d> (or unbounded if d < 1)",
        "  -tpar\t\tPhase folding + T-parallelization algorithm from [AMM14]",
        "  -cnotmin\tPhase folding + CNOT-minimization algorithm from [AAM17]",
        "  -clifford\t\t Re-synthesize Clifford segments",
        "  -O2\t\t**Standard strategy** Phase folding + simplify",
        "  -O3\t\tPhase folding + state folding + simplify + CNOT minimization",
        "  -O4\t\tPhase folding + state folding + simplify + Clifford resynthesis + CNOT minimization",
        "",
        "Benchmarking:",
        "  -benchmark <path>\tRun on all files in <folder> and output statistics",
        "  -apf\t\tAffine phase folding (Amy & Lunderville, POPL 2025)",
        "  -qpf\t\tQuadratic phase folding (Amy & Lunderville, POPL 2025)",
        "  -ppf\t\tPolynomial phase folding (Amy & Lunderville, POPL 2025)",
        "",
        "Misc:",
        "  -invgen <file>\tGenerates loop transition invariants and prints them",
        "",
        "E.g. \"feyn -verify -inline -cnotmin -simplify circuit.qc\" will first inline the circuit,",
        "       then optimize CNOTs, followed by a gate cancellation pass and finally verify the result",
        "",
        "Caution: Attempting to verify very large circuits can overload your system memory.",
        "         Set user-level memory limits when doing so."
      ]

defaultOptions :: Options
defaultOptions =
  Options
    { passes = [],
      verify = False,
      pureCircuit = False,
      useQASM3 = False
    }

parseArgs :: Bool -> Options -> [String] -> IO ()
parseArgs doneSwitches options [] = printHelp
parseArgs doneSwitches options (x : xs) = case x of
  f | doneSwitches -> runFile f
  "-h" -> printHelp
  "-purecircuit" -> parseArgs doneSwitches options {pureCircuit = True} xs
  "-inline" -> parseArgs doneSwitches options {passes = Inline : passes options} xs
  "-unroll" -> parseArgs doneSwitches options {passes = Unroll : passes options} xs
  "-mctExpand" -> parseArgs doneSwitches options {passes = MCT : passes options} xs
  "-toCliffordT" -> parseArgs doneSwitches options {passes = CT : passes options} xs
  "-simplify" -> parseArgs doneSwitches options {passes = Simplify : passes options} xs
  "-phasefold" -> parseArgs doneSwitches options {passes = Phasefold : passes options} xs
  "-statefold" -> parseArgs doneSwitches options {passes = (Statefold $ read (head xs)) : passes options} (tail xs)
  "-cnotmin" -> parseArgs doneSwitches options {passes = CNOTMin : passes options} xs
  "-tpar" -> parseArgs doneSwitches options {passes = TPar : passes options} xs
  "-clifford" -> parseArgs doneSwitches options {passes = Cliff : passes options} xs
  "-cxcz" -> parseArgs doneSwitches options {passes = CZ : passes options} xs
  "-decompile" -> parseArgs doneSwitches options {passes = Decompile : passes options} xs
  "-O2" -> parseArgs doneSwitches options {passes = o2 ++ passes options} xs
  "-O3" -> parseArgs doneSwitches options {passes = o3 ++ passes options} xs
  "-O4" -> parseArgs doneSwitches options {passes = o4 ++ passes options} xs
  "-apf" -> parseArgs doneSwitches options {passes = apf ++ passes options} xs
  "-qpf" -> parseArgs doneSwitches options {passes = qpf ++ passes options} xs
  "-ppf" -> parseArgs doneSwitches options {passes = ppf ++ passes options} xs
  "-verify" -> parseArgs doneSwitches options {verify = True} xs
  "-benchmark" -> benchmarkFolder (head xs) >>= runBenchmarks (benchPass options) (benchVerif options)
  "-qasm3" -> parseArgs doneSwitches options {useQASM3 = True} xs
  "-invgen" ->
    if takeExtension (head xs) == ".qasm"
      then generateInvariants (head xs)
      else putStrLn ("Must be a qasm file (" ++ (head xs) ++ ")") >> printHelp
  "--" -> parseArgs True options xs
  --  "VerBench"     -> runBenchmarks (benchPass [CNOTMin,Simplify]) (benchVerif True) benchmarksMedium
  --  "VerAlg"       -> runVerSuite
  "Small" -> runBenchmarks (benchPass options) (benchVerif options) benchmarksSmall
  "Med" -> runBenchmarks (benchPass options) (benchVerif options) benchmarksMedium
  "All" -> runBenchmarks (benchPass options) (benchVerif options) benchmarksAll
  "POPL25-affine" -> do
    putStrLn "Running circuit benchmarks..."
    runBenchmarks (benchPass defaultOptions {passes = apf}) (benchVerif defaultOptions {verify = True}) benchmarksPOPL25
    putStrLn "\nRunning program benchmarks..."
    runBenchmarksQASM (benchPass defaultOptions {passes = apf}) (benchVerif defaultOptions {useQASM3 = True}) benchmarksPOPL25QASM
  "POPL25-polynomial" -> do
    putStrLn "Running circuit benchmarks..."
    runBenchmarks (benchPass defaultOptions {passes = qpf}) (benchVerif defaultOptions {verify = True}) benchmarksPOPL25
    putStrLn "\nRunning additional unbounded optimization of fprenorm..."
    runBenchmarks (benchPass defaultOptions {passes = ppf}) (benchVerif defaultOptions {verify = True}) benchmarksPOPL25FP
    putStrLn "\nRunning program benchmarks..."
    runBenchmarksQASM (benchPass defaultOptions {passes = qpf}) (benchVerif defaultOptions {useQASM3 = True}) benchmarksPOPL25QASM
  "POPL25" -> do
    putStrLn "Running circuit benchmarks..."
    runBenchmarks (benchPass options) (benchVerif options) benchmarksPOPL25
    putStrLn "\nRunning program benchmarks..."
    runBenchmarksQASM (benchPass options) (benchVerif options {useQASM3 = True}) benchmarksPOPL25QASM
  f | ((drop (length f - 3) f) == ".qc") || ((drop (length f - 5) f) == ".qasm") -> runFile f
  f | otherwise -> putStrLn ("Unrecognized option \"" ++ f ++ "\"") >> printHelp
  where
    o2 = [Simplify, Phasefold, Simplify, CT, Simplify, MCT]
    o3 = [CNOTMin, Simplify, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]
    o4 = [CNOTMin, Cliff, PauliFold 1, Simplify, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]
    apf = [Simplify, PauliFold 1, Simplify, Statefold 1, Statefold 1, Phasefold, Simplify, CT, Simplify, MCT]
    qpf = [Simplify, PauliFold 1, Simplify, Statefold 2, Statefold 2, Phasefold, Simplify, CT, Simplify, MCT]
    ppf = [Simplify, PauliFold 1, Simplify, Statefold 0, Statefold 0, Phasefold, Simplify, CT, Simplify, MCT]
    runFile f | (takeExtension f) == ".qc"   = runPasses (dotQCPasses options) options f
    runFile f | (takeExtension f) == ".qasm" =
          if useQASM3 options
            then runPasses (qasm3Passes options) options f
            else runPasses (qasmPasses options) options f
    runFile f = putStrLn ("Unrecognized file type \"" ++ f ++ "\"") >> printHelp

main :: IO ()
main = getArgs >>= parseArgs False defaultOptions
