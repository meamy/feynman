module Tests where

import Data.List
import Numeric

import Data.Set (Set)
import qualified Data.Set as Set

import DotQC
import PhaseFold
import TPar
import Syntax (Primitive(CNOT, T, Tinv))

formmatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

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
  "cycle_17_3",
  "gf2^4_mult",
  "gf2^5_mult",
  "gf2^6_mult",
  "gf2^7_mult",
  "gf2^8_mult",
  "gf2^9_mult",
  "gf2^10_mult",
  "gf2^16_mult",
  "gf2^32_mult",
  "gf2^64_mult",
  "ham15-high",
  "ham15-low",
  "ham15-med",
  "hwb8",
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

printResults :: [(String, Either String [(Int, Int)])] -> IO ()
printResults xs =
  printResultsAcc (0, [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0]) xs

printResultsAcc :: (Int, [Float]) -> [(String, Either String [(Int, Int)])] -> IO ()
printResultsAcc avgs []     = do
  putStrLn "Averages:"
  printAverages avgs
  where
    printAverages (tot, (h:x:y:z:c:s:t:sw:[])) = do
      putStrLn $ "\tH:\t" ++ show (h / (fromIntegral tot))
      putStrLn $ "\tX:\t" ++ show (x / (fromIntegral tot))
      putStrLn $ "\tY:\t" ++ show (y / (fromIntegral tot))
      putStrLn $ "\tZ:\t" ++ show (z / (fromIntegral tot))
      putStrLn $ "\tCnot:\t" ++ show (c / (fromIntegral tot))
      putStrLn $ "\tS/S*:\t" ++ show (s / (fromIntegral tot))
      putStrLn $ "\tT/T*:\t" ++ show (t / (fromIntegral tot))
      putStrLn $ "\tSwap:\t" ++ show (sw / (fromIntegral tot))
printResultsAcc avgs (x:xs) = case x of
  (s, Left err) -> do
    putStrLn $ s ++ " -- Failed (" ++ err ++ ")"
    printResultsAcc avgs xs
  (s, Right cts) -> do
    putStrLn s
    printGateCounts cts
    printResultsAcc (updateAvg avgs cts) xs
  where
    pp x y = if isNaN x then y else if isNaN y then x else x + y
    chng (x,y)               = 100.0 * ((fromIntegral (x-y)) / (fromIntegral x))
    updateAvg (tot,tcts) cts = (tot+1, zipWith pp tcts $ map chng cts)
    showMod ct               = "\t" ++ show (chng ct) ++ "%"
    printGateCounts (h:x:y:z:c:s:t:sw:[]) = do
      putStrLn $ "\tH:\t" ++ (show $ fst h) ++ "/" ++ (show $ snd h) ++ showMod h
      putStrLn $ "\tX:\t" ++ (show $ fst x) ++ "/" ++ (show $ snd x) ++ showMod x
      putStrLn $ "\tY:\t" ++ (show $ fst y) ++ "/" ++ (show $ snd y) ++ showMod y
      putStrLn $ "\tZ:\t" ++ (show $ fst z) ++ "/" ++ (show $ snd z) ++ showMod z
      putStrLn $ "\tCnot:\t" ++ (show $ fst c) ++ "/" ++ (show $ snd c) ++ showMod c
      putStrLn $ "\tS/S*:\t" ++ (show $ fst s) ++ "/" ++ (show $ snd s) ++ showMod s
      putStrLn $ "\tT/T*:\t" ++ (show $ fst t) ++ "/" ++ (show $ snd t) ++ showMod t
      putStrLn $ "\tSwap:\t" ++ (show $ fst sw) ++ "/" ++ (show $ snd sw) ++ showMod sw

runBenchmarks :: (DotQC -> Either String (DotQC, DotQC)) -> [String] -> IO ()
runBenchmarks opt xs =
  let f s = do
        orig <- readFile $ benchmarksPath ++ s ++ ".qc"
        case printErr (parseDotQC orig) >>= opt of
          Left err      -> return $ (s, Left err)
          Right (c, c') -> return $ (s, Right $ zip (countGates c) (countGates c'))
      printErr res = case res of
        Left err -> Left $ show err
        Right x  -> Right x
  in
    mapM f xs >>= printResults

-- Testing
triv :: DotQC -> Either String (DotQC, DotQC)
triv circ = Right (circ, circ)

runPhaseFold :: DotQC -> Either String (DotQC, DotQC)
runPhaseFold qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = phaseFold q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in 
      Right (qc, ret)
      
runCnotMin :: DotQC -> Either String (DotQC, DotQC)
runCnotMin qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = gtpar cnotMinGray q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in
      Right (qc, ret)

runTpar :: DotQC -> Either String (DotQC, DotQC)
runTpar qc@(DotQC q i o decs) = case find (\(Decl n _ _) -> n == "main") decs of
  Nothing -> Left "Failed (no main function)"
  Just (Decl n p body) ->
    let gates  = toCliffordT body
        gates' = gtpar tparMore q (Set.toList i) gates
        main   = Decl n p $ fromCliffordT gates'
        ret    = qc { decls = map (\dec@(Decl n _ _) -> if n == "main" then main else dec) decs }
    in
      Right (qc, ret)
