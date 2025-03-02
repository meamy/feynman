{-# LANGUAGE TupleSections #-}
module Benchmarks where

import Data.List
import Data.Maybe (fromJust)
import Control.Monad (when)
import Numeric
import System.CPUTime (getCPUTime)
import System.Console.ANSI
import System.FilePath
import System.Directory
import Control.DeepSeq

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Array ((!), (//))
import qualified Data.Array as Array

import Control.Monad
import Data.Maybe

import Feynman.Frontend.DotQC hiding (gateCounts, tDepth)
import qualified Feynman.Frontend.DotQC as DotQC
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.TPar
import Feynman.Algebra.Linear
import Feynman.Synthesis.Reversible.Gray
import Feynman.Verification.Symbolic
import Feynman.Core (Primitive(CNOT, T, Tinv), Loc)

import qualified Data.BitVector as BitVector

import qualified Data.ByteString as B

import Control.Monad

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

{- Benchmark circuits -}
qcBenchmarksPath = "benchmarks/qc/"
qasm3BenchmarksPath = "benchmarks/qasm3/"

-- Benchmarks of up to 10 qubits
benchmarksSmall = map (qcBenchmarksPath ++) [
  "barenco_tof_3",
  "barenco_tof_4",
  "barenco_tof_5",
  "grover_5",
  "hwb6",
  "mod5_4",
  "mod_mult_55",
  "qft_4",
  "tof_3",
  "tof_4",
  "tof_5",
  "vbe_adder_3"
  ]

-- Benchmarks which don't crash the verifier
benchmarksMedium = benchmarksSmall ++ map (qcBenchmarksPath ++) [
  "adder_8",
  "barenco_tof_10",
  "csla_mux_3",
  "csum_mux_9",
  "gf2^4_mult",
  "gf2^5_mult",
  "gf2^6_mult",
  "gf2^7_mult",
  "gf2^8_mult",
  "gf2^9_mult",
  "gf2^10_mult",
  "gf2^16_mult",
  "gf2^32_mult",
  "ham15-high",
  "ham15-low",
  "ham15-med",
  "mod_adder_1024",
  "mod_red_21",
  "qcla_adder_10",
  "qcla_com_7",
  "qcla_mod_7",
  "rc_adder_6",
  --"shor_2_21",
  "tof_10"
  ]

-- Includes even the most ludicrous benchmarks
benchmarksAll = benchmarksMedium ++ map (qcBenchmarksPath ++) [
  "cycle_17_3",
  "gf2^64_mult",
  --"gf2^128_mult",
  --"gf2^256_mult",
  "hwb8",
  --"hwb10",
  --"hwb12",
  "mod_adder_1048576"
  ]

benchmarksPOPL25 = map (qcBenchmarksPath ++) [
  "grover_5",
  "mod5_4",
  "vbe_adder_3",
  "csla_mux_3",
  "csum_mux_9",
  "qcla_com_7",
  "qcla_mod_7",
  "qcla_adder_10",
  "adder_8",
  "rc_adder_6",
  "mod_red_21",
  "mod_mult_55",
  "mod_adder_1024",
  "gf2^4_mult",
  "gf2^5_mult",
  "gf2^6_mult",
  "gf2^7_mult",
  "gf2^8_mult",
  "gf2^9_mult",
  "gf2^10_mult",
  "gf2^16_mult",
 -- "gf2^32_mult",
  "ham15-low",
  "ham15-med",
  "ham15-high",
  "hwb6",
  "qft_4",
  "tof_3",
  "tof_4",
  "tof_5",
  "tof_10",
  "barenco_tof_3",
  "barenco_tof_4",
  "barenco_tof_5",
  "barenco_tof_10",
  "fprenorm"
  ]

benchmarksPOPL25QASM = map (qasm3BenchmarksPath ++) [
  "rus",
  "grover",
  "reset-simple",
  "if-simple",
  "loop-simple",
  "loop-h",
  "loop-nested",
  "loop-swap",
  "loop-nonlinear",
  "loop-null"
  ]

benchmarkFolder f = liftM (map ((f </>) . dropExtension) . filter (\s -> takeExtension s == ".qc")) $ getDirectoryContents f

{- Printing results -}

data BenchResult = BenchResult {
  size    :: Int,
  verRes  :: Maybe Bool,
  time    :: Double,
  counts  :: Map String (Int, Int),
  depths  :: (Int, Int),
  tdepths :: (Int, Int)
  }

printBenchmarks :: [(String, Either String BenchResult)] -> IO ()
printBenchmarks benchmarks = do
  (num, totals) <- foldM printResult (0, Map.empty) benchmarks
  putStrLn "Averages:"
  mapM_ (putStrLn . format) (Map.toList . Map.map (/ fromIntegral num) $ totals)
  where format (stat, avg) = "\t" ++ stat ++ ":\t\t" ++ show avg ++ "%"

printResult :: (Int, Map String Float) -> (String, Either String BenchResult) -> IO (Int, Map String Float)
printResult (num, totals) (benchmark, result) = case result of
  Left err -> do
    putStrLn $ benchmark ++ " -- Failed (" ++ err ++ ")"
    return (num, totals)
  Right result -> do
    putStrLn $ benchmark ++ ": " ++ show (size result) ++ " qubits, "
                        ++ formatFloatN (time result) 3 ++ "ms"
    case verRes result of
      Nothing -> return ()
      Just False -> do
        setSGR [SetColor Foreground Vivid Red]
        putStrLn "Fail"
        setSGR [Reset]
      Just True -> do
        setSGR [SetColor Foreground Vivid Green]
        putStrLn "Pass"
        setSGR [Reset]
    avgs      <- mapM printStat (Map.toList $ counts result)
    avgdepth  <- printStat ("Depth", depths result)
    avgtdepth <- printStat ("Tdepth", tdepths result)
    return (num+1, Map.unionsWith (+) (avgs ++ [avgdepth, avgtdepth, totals]))
  where printStat (stat, (orig, opt)) = do
          let diff = 100.0 * ((fromIntegral (orig-opt)) / (fromIntegral orig))
          putStrLn $ "\t" ++ stat ++ ":\t\t" ++ show orig ++ "/"
                          ++ show opt ++ "\t\t" ++ (if orig == 0 then "N/A" else show diff ++ "%")
          if orig == 0
            then return Map.empty
            else return $ Map.fromList [(stat, diff)]

{- Benchmarking functions -}
withTiming :: (() -> IO ()) -> IO ()
withTiming f = do
  start <- getCPUTime
  f ()
  end   <- getCPUTime
  let t = (fromIntegral $ end - start) / 10^9
  putStrLn $ "Time: " ++ formatFloatN t 3 ++ "ms"

runBenchmarks pass verify xs =
  let runBench s = do
        src   <- B.readFile $ s ++ ".qc"
        start <- getCPUTime
        case printErr (parseDotQC src) >>= \c -> pass c >>= \c' -> Right (c, c') of
          Left err      -> do
            putStrLn $ s ++ ": ERROR"
            return Nothing
          Right (c, c') ->
            let verResult = case verify of
                  Nothing -> ""
                  Just f  -> case f c c' of
                    Left  _ -> setSGRCode [SetColor Foreground Vivid Red] ++
                               " FAIL" ++
                               setSGRCode [Reset]
                    Right _ -> setSGRCode [SetColor Foreground Vivid Green] ++
                               " PASS" ++
                               setSGRCode [Reset]
                (glist, glist') = (fromCliffordT . toCliffordT . toGatelist $ c, toGatelist c')
                counts          = mergeCounts (DotQC.gateCounts $ glist) (DotQC.gateCounts glist')
                depths          = (depth glist, depth glist')
                tdepths         = (DotQC.tDepth glist, DotQC.tDepth glist')
            in do
              end  <- verResult `deepseq` counts `deepseq` getCPUTime
              let time = (fromIntegral $ end - start) / 10^9
              putStrLn $ s ++ ":" ++ verResult
              putStrLn $ "\tTime:\t\t" ++ formatFloatN time 3 ++ "ms"
              putStrLn $ "\tQubits:\t\t" ++ show (length $ qubits c)
              putStrLn $ "\tTotal gates:\t\t" ++ show (length $ glist) ++ "/" ++ show (length $ glist')
              gateRed   <- mapM printStat (Map.toList $ counts)
              depthRed  <- printStat ("Depth", depths)
              tdepthRed <- printStat ("Tdepth", tdepths)
              let (dir, name) = splitFileName s
                  outputDir = dir </> "opt"
                  outputPath = outputDir </> (name ++ "_opt.qc")
              createDirectoryIfMissing False outputDir
              writeFile outputPath (show c')
              return . Just $ Map.unionsWith (+) (gateRed ++ [depthRed, tdepthRed])
  in do
    results <- liftM catMaybes $ mapM runBench xs
    putStrLn "Averages:"
    mapM_ printAvg (Map.toList . Map.map (/ fromIntegral (length results)) . Map.unionsWith (+) $ results)
  where printErr res = case res of
          Left err -> Left $ show err
          Right x  -> Right x
        mergeCounts left right =
          let left'  = Map.map (,0) left
              right' = Map.map (0,) right
          in
            Map.unionWith (\(a, b) (c, d) -> (a+c, b+d)) left' right'
        printStat (stat, (orig, opt)) = do
            let diff = 100.0 * ((fromIntegral (orig-opt)) / (fromIntegral orig))
            putStrLn $ "\t" ++ stat ++ ":\t\t" ++ show orig ++ "/"
                            ++ show opt ++ "\t\t" ++ (if orig == 0 then "N/A" else formatFloatN diff 3 ++ "%")
            if orig == 0
            then return Map.empty
            else return $ Map.fromList [(stat, diff)]
        printAvg (stat, avg) = putStrLn $ "\t" ++ stat ++ ":\t\t" ++ formatFloatN avg 3 ++ "%"


qcBenchmarkRunner src pass = (parseDotQC src) >>= \c -> pass c >>= \c' -> Right (c, c')

