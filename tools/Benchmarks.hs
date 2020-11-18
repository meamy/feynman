{-# LANGUAGE TupleSections #-}
module Benchmarks where

import Data.List
import Data.Maybe (fromJust)
import Control.Monad (when)
import Numeric
import System.CPUTime (getCPUTime)
import System.Console.ANSI
import Control.DeepSeq

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Array ((!), (//))
import qualified Data.Array as Array

import Control.Monad
import Data.Maybe

import Feynman.Frontend.DotQC
import Feynman.Optimization.PhaseFold
import Feynman.Optimization.TPar
import Feynman.Algebra.Linear
import Feynman.Synthesis.Reversible.Gray
import Feynman.Verification.SOP
import Feynman.Core (Primitive(CNOT, T, Tinv))

import qualified Data.BitVector as BitVector
import Test.QuickCheck

import qualified Data.ByteString as B

import Control.Monad

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
  --"gf2^128_mult",
  --"gf2^256_mult",
  "hwb8",
  --"hwb10",
  --"hwb12",
  "mod_adder_1048576"
  ]

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
        src   <- B.readFile $ benchmarksPath ++ s ++ ".qc"
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
                counts          = mergeCounts (gateCounts $ glist) (gateCounts glist')
                depths          = (depth glist, depth glist')
                tdepths         = (tDepth glist, tDepth glist')
            in do
              end  <- verResult `deepseq` counts `deepseq` getCPUTime
              let time = (fromIntegral $ end - start) / 10^9
              putStrLn $ s ++ ":" ++ verResult
              putStrLn $ "\tTime:\t\t" ++ formatFloatN time 3 ++ "ms"
              putStrLn $ "\tQubits:\t\t" ++ show (length $ qubits c)
              gateRed   <- mapM printStat (Map.toList $ counts)
              depthRed  <- printStat ("Depth", depths)
              tdepthRed <- printStat ("Tdepth", tdepths)
              writeFile (benchmarksPath ++ "opt/" ++ s ++ "_opt.qc") (show c')
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


{- Benchmarking for [AAM17] -}

generateVecNonzero :: Int -> Gen F2Vec
generateVecNonzero n = do
  bits <- vector n
  if all not bits
    then generateVecNonzero n
    else return $ F2Vec $ BitVector.fromBits bits

generateVecNonunital :: Int -> Gen F2Vec
generateVecNonunital n = do
  bits <- vector n
  if (length . filter (True==)) bits <= 1
    then generateVecNonunital n
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
  let (circ, []) = cnotMinGray ist ist (zip (Set.toList set) (repeat 1)) []
  return $ countCNOTs circ

runDouble :: Int -> Int -> IO (Int, Int)
runDouble n m = do
  let ids = map show [1..n]
  let ist = genInitSt ids
  set <- generate $ generateSizedSet n m
  let (circ, []) = cnotMinGray ist ist (zip (Set.toList set) (repeat 1)) []
  let circ' = bruteForceASkeleton ids set ist
  when (not $ check ids ist set circ) $ putStrLn "WARNING"
  return $ (countCNOTs circ, countCNOTs $ fromJust circ')

runExperiment :: Int -> Int -> Int -> IO ()
runExperiment n m repeats = do
  results <- mapM (\_ -> runSingle n m) [1..repeats]
  let avg = (fromIntegral (foldr (+) 0 results)) / (fromIntegral repeats)
  putStrLn $ "  |S| = " ++ (show m) ++ ": " ++ (show avg)
  
runExperiments :: Int -> Int -> IO ()
runExperiments n repeats = do
  putStrLn $ "Running experiments for n=" ++ (show n) ++ ", " ++ (show repeats) ++ " repetitions"
  sequence_ $ map (\m -> runExperiment n m repeats) ([0,2^(n-5)..2^n-1] ++ [2^n-1])

runExperiment2 :: Int -> Int -> Int -> IO ()
runExperiment2 n m repeats = do
  results <- mapM (\_ -> runDouble n m) [1..repeats]
  let avg lst = (fromIntegral (foldr (+) 0 lst)) / (fromIntegral repeats) :: Float
  let avgs = (avg . fst $ unzip results, avg . snd $ unzip results)
  putStrLn $ "  |S| = " ++ (show m) ++ ": " ++ (show avgs)
  
runExperiments2 :: Int -> Int -> IO ()
runExperiments2 n repeats = do
  putStrLn $ "Running experiments for n=" ++ (show n) ++ ", " ++ (show repeats) ++ " repetitions"
  sequence_ $ map (\m -> runExperiment2 n m repeats) [1..2^n-1]

powerset set
  | Set.null set = Set.singleton Set.empty
  | otherwise    = Set.union ps (Set.map (Set.insert x) ps)
    where (x, xs) = Set.deleteFindMin set
          ps      = powerset xs

allSubsets = powerset . Set.deleteMin . Set.fromList . allVecs
mostSubsets = powerset . Set.filter ((1 <) . wt) . Set.fromList . allVecs
someSubsets = powerset . Set.filter ((6 >) . wt) . Set.fromList . allVecs

computeMinAll n = Set.foldr (\x -> Map.insert x $ bruteForceASkeleton ids x ist) Map.empty pow
  where ids = map show [1..n]
        ist = genInitSt ids
        pow = someSubsets n

computeAlgAll n = Set.foldr f Map.empty pow
  where f x = Map.insert x . fst $ cnotMinGray ist ist (zip (Set.toList x) (repeat 1)) []
        ids = map show [1..n]
        ist = genInitSt ids
        pow = allSubsets n

computeHist = Map.mapKeysWith (++) (Set.size) . Map.map (\m -> [m])

computeAvg :: Map Int [[Primitive]] -> Map Int Double
computeAvg  = Map.map (\circs -> fromIntegral (sumLengths circs) / fromIntegral (length circs))
  where sumLengths = foldr (\c -> (countCNOTs c +)) 0

-- Finds all n-qubit minimal skeletons
coverIt n =
  let cnots = [(i, j) | i <- [0..n-1], j <- [0..n-1], i /= j]
      extendByCnot (skel, st) (i, j) =
        let j' = st!i + st!j in
          (Set.insert j' skel, st//[(j, j')])
      doit i (seen, minMap, newhorizon) (st, cnot) =
        let st' = extendByCnot st cnot in
          if Set.member st' seen
          then (seen, minMap, newhorizon)
          else (Set.insert st' seen,
                if (snd st' == iarr)
                then Set.foldr (\set -> Map.insertWith min set i) minMap (powerset $ fst st')
                else minMap,
                st':newhorizon)
      iterate (seen, minMap, horizon) i =
          foldl' (doit i) (seen, minMap, []) [(st, cnot) | st <- horizon, cnot <- cnots]
      iarr = Array.array (0, n-1) [(i, bitI n i) | i <- [0..n-1]]
      ist = (Set.fromList . Array.elems $ iarr, iarr)
      imap = Set.foldr (\set -> Map.insert set 0) Map.empty $ powerset (fst ist)
      (_, minMap, _) = foldl' iterate (Set.singleton ist, imap, [ist]) [1..2^n-1]
  in
    Map.mapWithKey (\k v -> fromIntegral (foldr (+) 0 v) / fromIntegral (length v)). Map.mapKeysWith (++) (Set.size) . Map.map (\m -> [m]) $ minMap

-- Finds all n-qubit minimal skeletons
coverItOpen n =
  let cnots = [(i, j) | i <- [0..n-1], j <- [0..n-1], i /= j]
      extendByCnot (skel, st) (i, j) =
        let j' = st!i + st!j in
          (Set.insert j' skel, st//[(j, j')])
      doit i (seen, minMap, newhorizon) (st, cnot) =
        let st' = extendByCnot st cnot in
          if Set.member st' seen
          then (seen, minMap, newhorizon)
          else (Set.insert st' seen,
                Set.foldr (\set -> Map.insertWith min set i) minMap (powerset $ fst st'),
                st':newhorizon)
      iterate (seen, minMap, horizon) i =
          foldl' (doit i) (seen, minMap, []) [(st, cnot) | st <- horizon, cnot <- cnots]
      iarr = Array.array (0, n-1) [(i, bitI n i) | i <- [0..n-1]]
      ist = (Set.fromList . Array.elems $ iarr, iarr)
      imap = Set.foldr (\set -> Map.insert set 0) Map.empty $ powerset (fst ist)
      (_, minMap, _) = foldl' iterate (Set.singleton ist, imap, [ist]) [1..2^n-n]
  in
    Map.mapWithKey (\k v -> fromIntegral (foldr (+) 0 v) / fromIntegral (length v)). Map.mapKeysWith (++) (Set.size) . Map.map (\m -> [m]) $ minMap

bruteForceEfficient n s =
  let cnots = [(i, j) | i <- [0..n-1], j <- [0..n-1], i /= j]
      extendByCnot (skel, st, circ) (i, j) =
        let j' = st!i + st!j in
          (Set.insert j' skel, st//[(j, j')], circ ++ [CNOT (show i) (show j)])
      doit i (seen, minMap, newhorizon) ((skel, st, circ), cnot) =
        let (skel', st', circ') = extendByCnot (skel, st, circ) cnot in
          if Set.member (skel', st') seen
          then Right (seen, minMap, newhorizon)
          else if Set.isSubsetOf s (skel') && st' == iarr
               then Left circ'
               else Right $
                 (Set.insert (skel', st') seen,
                  if (st' == iarr)
                  then Set.foldr (\set -> Map.insertWith min set i) minMap (powerset skel')
                  else minMap,
                  (skel', st', circ'):newhorizon)
      iterate (seen, minMap, horizon) i =
          foldM (doit i) (seen, minMap, []) [((skel, st, circ), cnot) | (skel, st, circ) <- horizon, cnot <- cnots]
      iskel = Set.fromList . Array.elems $ iarr
      iarr = Array.array (0, n-1) [(i, bitI n i) | i <- [0..n-1]]
      imap = Set.foldr (\set -> Map.insert set 0) Map.empty $ powerset iskel
  in
    foldM iterate (Set.singleton (iskel, iarr), imap, [(iskel, iarr, [])]) [1..2^n-1]

{- Functional verification suite from [A18] -}

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
  s <- B.readFile fname
  case parseDotQC s of
    Left err -> putStrLn (show err) >> return []
    Right c  ->
      case find (\(Feynman.Frontend.DotQC.Decl n _ _) -> n == "main") (Feynman.Frontend.DotQC.decls c) of
        Nothing -> putStrLn "No main function!" >> return []
        Just (Feynman.Frontend.DotQC.Decl _ _ body) -> return $ toCliffordT body
