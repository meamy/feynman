{-# LANGUAGE TupleSections #-}
module Benchmarks where

import Data.List
import Numeric
import System.Time

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad

import Frontend.DotQC
import Optimization.PhaseFold
import Optimization.TPar
import Algebra.Linear
import Synthesis.Reversible.Gray
import Verification.SOP
import Core (Primitive(CNOT, T, Tinv))

import qualified Data.BitVector as BitVector
import Test.QuickCheck

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

{- Benchmark circuits -}
benchmarksPath = "benchmarks/"

-- Benchmarks of up to 10 qubits
benchmarksSmall = [
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
benchmarksMedium = benchmarksSmall ++ [
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
benchmarksAll = benchmarksMedium ++ [
  "cycle_17_3",
  "gf2^64_mult",
  "gf2^128_mult",
  "gf2^256_mult",
  "hwb8",
  "hwb10",
  "hwb12",
  "mod_adder_1048576"
  ]

{- Printing results -}

data BenchResult = BenchResult {
  size    :: Int,
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
  TOD starts startp <- getClockTime
  f ()
  TOD ends endp <- getClockTime
  let t = (fromIntegral $ ends - starts)*1000 + (fromIntegral $ endp - startp)/10^9
  putStrLn $ "Time: " ++ formatFloatN t 3 ++ "ms"

runBenchmarks :: (DotQC -> Either String DotQC) -> [String] -> IO ()
runBenchmarks pass xs =
  let f s = do
        src <- readFile $ benchmarksPath ++ s ++ ".qc"
        TOD starts startp <- getClockTime
        case printErr (parseDotQC src) of
          Left err -> return $ (s, Left err)
          Right c  -> case pass c of
            Left err -> return $ (s, Left err)
            Right c' -> do
              writeFile (benchmarksPath ++ "opt/" ++ s ++ "_opt.qc") (show c')
              TOD ends endp  <- getClockTime
              let (glist, glist') = (fromCliffordT . toCliffordT . toGatelist $ c, toGatelist c')
              let result = BenchResult {
                    size    = length (qubits c),
                    time    = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9,
                    counts  = mergeCounts (gateCounts $ glist) (gateCounts glist'),
                    depths  = (depth glist, depth glist'),
                    tdepths = (tDepth glist, tDepth glist') }
              return $ (s, Right result)
      printErr res = case res of
        Left err -> Left $ show err
        Right x  -> Right x
  in
    mapM f xs >>= printBenchmarks
  where mergeCounts left right =
          let left'  = Map.map (,0) left
              right' = Map.map (0,) right
          in
            Map.unionWith (\(a, b) (c, d) -> (a+c, b+d)) left' right'

runVertest :: (DotQC -> Either String DotQC) -> (DotQC -> DotQC -> Either String DotQC) -> [String] -> IO ()
runVertest pass verify xs =
  let f s = do
        src <- readFile $ benchmarksPath ++ s ++ ".qc"
        case printErr (parseDotQC src) of
          Left err -> return $ (s, Left err)
          Right c  -> case pass c of
            Left err -> return $ (s, Left err)
            Right c' -> do
              TOD starts startp <- getClockTime
              case verify c c' of
                Left err -> putStrLn $ "Failed to verify: " ++ s
                Right _  -> return ()
              TOD ends endp  <- getClockTime
              let (glist, glist') = (fromCliffordT . toCliffordT . toGatelist $ c, toGatelist c')
              let result = BenchResult {
                    size    = length (qubits c),
                    time    = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9,
                    counts  = mergeCounts (gateCounts $ glist) (gateCounts glist'),
                    depths  = (depth glist, depth glist'),
                    tdepths = (tDepth glist, tDepth glist') }
              return $ (s, Right result)
      printErr res = case res of
        Left err -> Left $ show err
        Right x  -> Right x
  in
    mapM f xs >>= printBenchmarks
  where mergeCounts left right =
          let left'  = Map.map (,0) left
              right' = Map.map (0,) right
          in
            Map.unionWith (\(a, b) (c, d) -> (a+c, b+d)) left' right'

-- Random benchmarks
generateVecNonzero :: Int -> Gen F2Vec
generateVecNonzero n = do
  bits <- vector n
  if all not bits
    then generateVecNonzero n
    else return $ F2Vec $ BitVector.fromBits bits

generateSizedSet :: Int -> Int -> Gen (Set F2Vec)
generateSizedSet n m =
  let f set = if Set.size set >= m then return set else
        do
          bits <- generateVecNonzero n
          f $ Set.insert bits set
  in
    f Set.empty

countCNOTs :: [Primitive] -> Int
countCNOTs = length . filter iscnot
  where iscnot (CNOT _ _) = True
        iscnot _          = False

runSingle :: Int -> Int -> IO (Int)
runSingle n m = do
  let ids = map show [1..n]
  let ist = genInitSt ids
  set <- generate $ generateSizedSet n m
  let circ = cnotMinGray ist ist $ zip (Set.toList set) (repeat 1)
  return $ countCNOTs circ

runExperiment :: Int -> Int -> Int -> IO ()
runExperiment n m repeats = do
  results <- mapM (\_ -> runSingle n m) [1..repeats]
  let avg = (fromIntegral (foldr (+) 0 results)) / (fromIntegral repeats)
  putStrLn $ "  |S| = " ++ (show m) ++ ": " ++ (show avg)
  
runExperiments :: Int -> Int -> IO ()
runExperiments n repeats = do
  putStrLn $ "Running experiments for n=" ++ (show n) ++ ", " ++ (show repeats) ++ " repetitions"
  sequence_ $ map (\m -> runExperiment n m repeats) [1..2^n-1]

runVerSuite :: IO ()
runVerSuite = do
  withTiming (verifyToffoliN 50)
  withTiming (verifyToffoliN 100)
  withTiming (verifyMaslovN 50)
  withTiming (verifyMaslovN 100)
  withTiming (verifyOOPAdder 8)
  withTiming (verifyOOPAdder 16)
  withTiming (verifyHiddenShift 20 4)
  withTiming (verifyHiddenShift 40 5)
  withTiming (verifyHiddenShift 60 10)
  withTiming (verifyHiddenShiftQuantum 20 4)
  withTiming (verifyHiddenShiftQuantum 40 5)
  withTiming (verifyHiddenShiftQuantum 60 10)

{- Utilities for interactive debugging -}

gatelistOfFile :: String -> IO [Primitive]
gatelistOfFile fname = do
  s <- readFile fname
  case parseDotQC s of
    Left err -> putStrLn (show err) >> return []
    Right c  ->
      case find (\(Frontend.DotQC.Decl n _ _) -> n == "main") (Frontend.DotQC.decls c) of
        Nothing -> putStrLn "No main function!" >> return []
        Just (Frontend.DotQC.Decl _ _ body) -> return $ toCliffordT body
