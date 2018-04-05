module Tests where

import Data.List
import Numeric
import System.Time

import Data.Set (Set)
import qualified Data.Set as Set

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

benchmarksPath = "benchmarks/"

{- Benchmarks of up to 10 qubits -}
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

{- Most benchmarks, should be runnable with any optimization -}
benchmarksMedium = benchmarksSmall ++ [
  "adder_8",
  "barenco_tof_10",
  "csla_mux_3",
  "csum_mux_9",
--  "cycle_17_3",
  "gf2^4_mult",
  "gf2^5_mult",
  "gf2^6_mult",
  "gf2^7_mult",
  "gf2^8_mult",
  "gf2^9_mult",
  "gf2^10_mult",
  "gf2^16_mult",
  "gf2^32_mult",
--  "gf2^64_mult",
  "ham15-high",
  "ham15-low",
  "ham15-med",
--  "hwb8",
  "mod_adder_1024",
  "mod_red_21",
  "qcla_adder_10",
  "qcla_com_7",
  "qcla_mod_7",
  "rc_adder_6",
  --"shor_2_21",
  "tof_10"
  ]

{- Includes even the most ludicrous benchmarks -}
benchmarksAll = benchmarksMedium ++ [
  "gf2^128_mult",
  "gf2^256_mult",
  "hwb10",
  "hwb12",
  "mod_adder_1048576"
  ]

printResults :: [(String, Either String (Int, Double, [(Int, Int)]))] -> IO ()
printResults xs =
  printResultsAcc (0, [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) xs

printResultsAcc :: (Int, [Float]) -> [(String, Either String (Int, Double, [(Int, Int)]))] -> IO ()
printResultsAcc avgs []     = do
  putStrLn "Averages:"
  printAverages avgs
  where
    printAverages (tot, (h:x:y:z:c:s:t:sw:td:[])) = do
      putStrLn $ "\tH:\t" ++ show (h / (fromIntegral tot))
      putStrLn $ "\tX:\t" ++ show (x / (fromIntegral tot))
      putStrLn $ "\tY:\t" ++ show (y / (fromIntegral tot))
      putStrLn $ "\tZ:\t" ++ show (z / (fromIntegral tot))
      putStrLn $ "\tCnot:\t" ++ show (c / (fromIntegral tot))
      putStrLn $ "\tS/S*:\t" ++ show (s / (fromIntegral tot))
      putStrLn $ "\tT/T*:\t" ++ show (t / (fromIntegral tot))
      putStrLn $ "\tSwap:\t" ++ show (sw / (fromIntegral tot))
      putStrLn $ "\tT-depth:\t" ++ show (td / (fromIntegral tot))
printResultsAcc avgs (x:xs) = case x of
  (s, Left err) -> do
    putStrLn $ s ++ " -- Failed (" ++ err ++ ")"
    printResultsAcc avgs xs
  (s, Right (n, t, cts)) -> do
    putStrLn $ s ++ ": " ++ (show n) ++ " qubits, " ++ (formatFloatN t 3)  ++ "ms"
    printGateCounts cts
    printResultsAcc (updateAvg avgs cts) xs
  where
    pp x y = if isNaN x then y else if isNaN y then x else x + y
    chng (x,y)               = 100.0 * ((fromIntegral (x-y)) / (fromIntegral x))
    updateAvg (tot,tcts) cts = (tot+1, zipWith pp tcts $ map chng cts)
    showMod ct               = "\t" ++ show (chng ct) ++ "%"
    printGateCounts (h:x:y:z:c:s:t:sw:td:[]) = do
      putStrLn $ "\tH:\t" ++ (show $ fst h) ++ "/" ++ (show $ snd h) ++ showMod h
      putStrLn $ "\tX:\t" ++ (show $ fst x) ++ "/" ++ (show $ snd x) ++ showMod x
      putStrLn $ "\tY:\t" ++ (show $ fst y) ++ "/" ++ (show $ snd y) ++ showMod y
      putStrLn $ "\tZ:\t" ++ (show $ fst z) ++ "/" ++ (show $ snd z) ++ showMod z
      putStrLn $ "\tCnot:\t" ++ (show $ fst c) ++ "/" ++ (show $ snd c) ++ showMod c
      putStrLn $ "\tS/S*:\t" ++ (show $ fst s) ++ "/" ++ (show $ snd s) ++ showMod s
      putStrLn $ "\tT/T*:\t" ++ (show $ fst t) ++ "/" ++ (show $ snd t) ++ showMod t
      putStrLn $ "\tSwap:\t" ++ (show $ fst sw) ++ "/" ++ (show $ snd sw) ++ showMod sw
      putStrLn $ "\tT-depth:\t" ++ (show $ fst td) ++ "/" ++ (show $ snd td) ++ showMod td

withTiming :: (() -> IO ()) -> IO ()
withTiming f = do
  TOD starts startp <- getClockTime
  f ()
  TOD ends endp <- getClockTime
  let t = (fromIntegral $ ends - starts)*1000 + (fromIntegral $ endp - startp)/10^9
  putStrLn $ "Time: " ++ formatFloatN t 3 ++ "ms"

runBenchmarks :: ((DotQC, DotQC) -> Either String (DotQC, DotQC)) -> [String] -> IO ()
runBenchmarks opt xs =
  let f s = do
        orig  <- readFile $ benchmarksPath ++ s ++ ".qc"
        TOD starts startp <- getClockTime
        case printErr (parseDotQC orig) >>= (\c -> opt (c, c)) of
          Left err      -> return $ (s, Left err)
          Right (c, c') -> do
            writeFile (benchmarksPath ++ "opt/" ++ s ++ "_opt.qc") (show c')
            TOD ends endp  <- getClockTime
            let diff = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
            return $ (s, Right $ (length (qubits c), diff, zip (countGates c) (countGates c') ++ [(tDepth c, tDepth c')]))
      printErr res = case res of
        Left err -> Left $ show err
        Right x  -> Right x
  in
    mapM f xs >>= printResults

runVertest :: [String] -> IO ()
runVertest xs =
  let f s = do
        orig  <- readFile $ benchmarksPath ++ s ++ ".qc"
        case printErr (parseDotQC orig) >>= (\c -> runCnotMin (c, c)) of
          Left err      -> return $ (s, Left err)
          Right (c, c') -> do
            TOD starts startp <- getClockTime
            case runVerification (c, c') of
              Left err -> putStrLn $ "Failed to verify: " ++ s
              Right _  -> return ()
            TOD ends endp  <- getClockTime
            let diff = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
            return $ (s, Right $ (length (qubits c), diff, zip (countGates c) (countGates c') ++
                                                                               [(tDepth c, tDepth c')]))
      printErr res = case res of
        Left err -> Left $ show err
        Right x  -> Right x
  in
    mapM f xs >>= printResults

-- Testing
triv :: (DotQC, DotQC) -> Either String (DotQC, DotQC)
triv (_, circ) = Right (circ, circ)

runPhaseFold :: (DotQC, DotQC) -> Either String (DotQC, DotQC)
runPhaseFold (c, qc@(DotQC q i o decs)) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = phaseFold q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in 
      Right (c, ret)
      
runTpar :: (DotQC, DotQC) -> Either String (DotQC, DotQC)
runTpar (c, qc@(DotQC q i o decs)) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = tpar q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in
      Right (c, ret)

runCnotMin :: (DotQC, DotQC) -> Either String (DotQC, DotQC)
runCnotMin (c, qc@(DotQC q i o decs)) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = minCNOT q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in
      Right (c, ret)

runVerification :: (DotQC, DotQC) -> Either String (DotQC, DotQC)
runVerification (qc1@(DotQC q1 i1 o1 decs1), qc2@(DotQC q2 i2 o2 decs2)) =
  case (\f -> (f decs1, f decs2)) $ find (\(Decl n _ _) -> n == "main") of
  (Nothing, _) -> Left "Failed (no main function)"
  (_, Nothing) -> Left "Failed (no main function)"
  (Just (Decl n1 p1 body1), Just (Decl n2 p2 body2)) ->
    let gates1 = toCliffordT body1
        gates2 = toCliffordT body2
    in
      case validate q1 (Set.toList i1) gates1 gates2 of
        Nothing  -> Right (qc1, qc2)
        Just sop -> Left $ "Failed to validate: " ++ show sop

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

-- Utilities for interactive debugging and testing

gatelistOfFile :: String -> IO [Primitive]
gatelistOfFile fname = do
  s <- readFile fname
  case parseDotQC s of
    Left err -> putStrLn (show err) >> return []
    Right c  ->
      case find (\(Frontend.DotQC.Decl n _ _) -> n == "main") (Frontend.DotQC.decls c) of
        Nothing -> putStrLn "No main function!" >> return []
        Just (Frontend.DotQC.Decl _ _ body) -> return $ toCliffordT body
