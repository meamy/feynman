module Feynman.Synthesis.HypergraphPartition.Report where
import Feynman.Core (Primitive(..), ID, Vertex(..), isZBasisPhaseGate)
import Feynman.Algebra.Linear
import Feynman.Synthesis.HypergraphPartition.DistributedSynthesis

import Data.List (groupBy, intercalate, sortBy)

import qualified Data.Map as Map

import Data.IORef (IORef, newIORef, modifyIORef', atomicModifyIORef')
import System.IO.Unsafe (unsafePerformIO)


{-# NOINLINE distReport #-}
distReport :: IORef [String]
distReport = unsafePerformIO (newIORef [])

-- Record one line of the distribution report.
reportDist :: String -> IO ()
reportDist line = modifyIORef' distReport (++ [line])

-- Take the recorded lines, clearing them for the next run.
takeDistReport :: IO [String]
takeDistReport = atomicModifyIORef' distReport (\ls -> ([], ls))

showParity :: [ID] -> F2Vec -> String
showParity ids p =
  case [ q | (i, q) <- zip [0 ..] ids, p @. i ] of
    [] -> "0"
    qs -> intercalate "+" qs

reportInputParities :: [ID] -> [Primitive] -> IO ()
reportInputParities ids circ = do
  let parities = concatMap chunkParities (summarizeChunks ids circ)
  reportDist $ "Parities (" ++ show (length parities) ++ "): "
               ++ intercalate ", " (map (showParity ids) parities)

-- | Report, chunk by chunk, what each synthesis step produces for the chosen
-- split. Recomputes the same intermediate values synthesizeUnderQubitSplit uses.
-- Call it once on the final split, never inside the search.
reportSynthesisSteps :: [Primitive] -> [ID] -> [ID] -> IO ()
reportSynthesisSteps circ ids0 ids1 = mapM_ step (zip [1 :: Int ..] chunks)
  where
    sortedIds = ids0 ++ ids1
    numQpu0   = length ids0
    n         = length sortedIds
    onQpu0 q  = q `elem` ids0
    shw       = showParity sortedIds
    list xs   = if null xs then "none" else intercalate ", " xs

    isPP (CNOT _ _) = True
    isPP g          = isZBasisPhaseGate g
    chunks = groupBy (\g1 g2 -> isPP g1 == isPP g2) circ

    mask0 = fromBits (reverse [ i <  numQpu0 | i <- [0 .. n - 1] ])
    mask1 = fromBits (reverse [ i >= numQpu0 | i <- [0 .. n - 1] ])

    step (k, chunk)
      | not (isPP (head chunk)) =
          reportDist $ "Chunk " ++ show k ++ " (copied as-is): " ++ list (map show chunk)
      | otherwise = do
          let (phases, finalMat) = extractPhasesAndMatrix sortedIds chunk (identity n)
              (s0, s1, mv) = matroidPhaseSplit mask0 mask1 (map fst phases)
              imports s lm rm = if null s then [] else toList (snd (rewriteParities s lm rm))
              imp0         = imports s0 mask0 mask1
              imp1         = imports s1 mask1 mask0
              bRows        = [ q ++ " <- " ++ shw r
                             | (q, r) <- zip sortedIds (toList finalMat), shw r /= q ]

              -- The same calls synthDistributedMatroid / distSynth make.
              parityToPart = Map.fromList ([ (p, 0) | p <- s0 ] ++ [ (p, 1) | p <- s1 ])
              localQIdx    = Map.fromList (zip sortedIds [1 ..])
              localPart    = Map.fromList [ (Wire i, if i <= numQpu0 then 0 else 1) | i <- [1 .. n] ]
              (phaseGates, phaseBells) =
                synthPhases sortedIds numQpu0 phases parityToPart localQIdx localPart
              rawLinear    = synthDistributedLinear sortedIds finalMat numQpu0
              env          = Map.fromList [ (q, if onQpu0 q then 0 else 1) | q <- sortedIds ]
              (routedLinear, linearBells) =
                routeLinearGates rawLinear (length phaseBells `div` 2) env
              resets       = [ Reset b | b <- phaseBells ++ linearBells ]
              ebits        = (length phaseBells + length linearBells) `div` 2

              crossCnots   = [ c ++ " -> " ++ t | CNOT c t <- rawLinear, onQpu0 c /= onQpu0 t ]
              gates gs     = list (map show gs)
          reportDist $ "Chunk " ++ show k ++ " (resynthesized, " ++ show (length chunk) ++ " gates)"
          reportDist $ "  original gates:         " ++ gates chunk
          reportDist $ "  extractPhasesAndMatrix  phases: "
                       ++ list [ shw p ++ " : " ++ show a | (p, a) <- phases ]
          reportDist $ "  extractPhasesAndMatrix  B: "
                       ++ (if null bRows then "identity" else intercalate ", " bRows)
          reportDist $ "  matroidPhaseSplit       QPU 0 computes: " ++ list (map shw s0)
          reportDist $ "  matroidPhaseSplit       QPU 1 computes: " ++ list (map shw s1)
          reportDist $ "  matroidPhaseSplit       value: " ++ show mv
          reportDist $ "  synthPhases             QPU 0 imports: " ++ list (map shw imp0)
          reportDist $ "  synthPhases             QPU 1 imports: " ++ list (map shw imp1)
          reportDist $ "  synthPhases             gates: " ++ gates phaseGates
          reportDist $ "  synthDistributedLinear  gates: " ++ gates rawLinear
          reportDist $ "  synthDistributedLinear  cross-QPU CNOTs: " ++ list crossCnots
          reportDist $ "  routeLinearGates        gates: " ++ gates routedLinear
          reportDist $ "  distSynth               resets: " ++ gates resets
          reportDist $ "  distSynth               ebits: " ++ show ebits
                       ++ " (phase " ++ show (length imp0 + length imp1)
                       ++ ", linear " ++ show (length crossCnots) ++ ")"

reportQpus :: [ID] -> [ID] -> IO ()
reportQpus ids0 ids1 = do
  reportDist $ "QPU 0 (" ++ show (length ids0) ++ " qubits): " ++ unwords (sortBy compare ids0)
  reportDist $ "QPU 1 (" ++ show (length ids1) ++ " qubits): " ++ unwords (sortBy compare ids1)

reportDistribution :: Bool -> IO ()
reportDistribution ok =
  reportDist $ "Distribution: " ++ (if ok then "PASS" else "FAILED (cross-partition gate)")