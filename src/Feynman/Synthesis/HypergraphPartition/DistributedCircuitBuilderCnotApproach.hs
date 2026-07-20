module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilderCnotApproach where


import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import Feynman.Core (Primitive(..), getArgs, ID, isCZ, isCNOT,isZBasisPhaseGate, Block, Vertex(..), Hypergraph(..), Hyperedge, substGate, PartitionData, Circuit (qubits))
import Feynman.Algebra.Linear
import Feynman.Synthesis.Reversible(linearSynth, toParity, Phase)
import qualified Feynman.Synthesis.Reversible.Gray as Gray

import Feynman.Optimization.TPar (AnalysisState(..), applyGate)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath ((</>))

import Data.List (sortBy, groupBy, foldl', minimumBy, nub)
import Data.Ord (comparing)

import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict (runState)
import Control.Monad (foldM)


initBellPairs :: ID -> ID -> [Primitive]
initBellPairs bell1 bell2 = [H bell1, CNOT bell1 bell2]

catEntangler :: ID -> ID -> ID -> [Primitive]
catEntangler srcQubit bell1 bell2 =
    initBellPairs bell1 bell2 ++ [CNOT srcQubit bell2, Measure bell2, CNOT bell2 bell1]

catDisentangler :: ID -> ID -> [Primitive]
catDisentangler srcQubit bell = [H bell,Measure bell,CZ bell srcQubit]

catEntanglerMulti :: [ID] -> ID -> ID -> [Primitive]
catEntanglerMulti srcQubits bell1 bell2 =
    [H bell1, CNOT bell1 bell2] ++
    [CNOT src bell2 | src <- srcQubits] ++
    [Measure bell2, CNOT bell2 bell1]


catDisentanglerMulti :: [ID] -> ID -> [Primitive]
catDisentanglerMulti srcQubits bell = 
    [H bell, Measure bell] ++
    [CZ bell src | src <- srcQubits]

quasiSwap:: ID -> ID -> [Primitive]
quasiSwap qubit1 qubit2 = [CNOT qubit1 qubit2, CNOT qubit2 qubit1]

-- Phase corrections for the control sets
phaseCorrection:: ID -> Set ID -> [Primitive]
phaseCorrection ctrlQubit s = [CZ ctrlQubit c | c <- Set.toList s]

targetDisentangler :: ID -> ID -> ID -> ID -> Set ID -> [Primitive]
targetDisentangler a sA f1 f2 s =
    catEntangler sA f1 f2 ++ [Reset f2] ++ quasiSwap a f1 ++ [H f1,Measure f1] ++
    phaseCorrection f1 s ++ catDisentangler a sA

getTeleportationBoundaries :: Hypergraph -> Map Vertex Block -> [(Vertex, Int, Int)]
getTeleportationBoundaries (Hypergraph _ hedges) partMap = concatMap (analyzeEdge . fst) hedges
  where
    analyzeEdge hedge =
      let vertices = Set.toList hedge
          wires    = [w | w@(Wire _) <- vertices]
          gates    = [g | GateIdx g <- vertices]
      in case wires of
           [wire] ->
             let wirePart = Map.findWithDefault 0 wire partMap
                 partOf g = Map.findWithDefault 0 (GateIdx g) partMap

                 -- ALL non-local gates, in chronological order, tagged with their server.
                 tagged = [ (g, partOf g)
                          | g <- sortBy compare gates
                          , partOf g /= wirePart ]

                 -- Group only CONSECUTIVE gates that share a server. This guarantees the
                 -- emitted [start,end] windows on one wire never overlap, which is what
                 -- synthesizeDQC's single-active-bell-per-wire model requires.
                 grouped = groupBy (\(_,p1) (_,p2) -> p1 == p2) tagged

                 makeBoundary grp = (wire, fst (head grp), fst (last grp))
             in map makeBoundary grouped
           _ -> []


annotateCircuit :: [Primitive] -> Int -> [(Primitive, Maybe Int)]
annotateCircuit circ numQubits =
  let cnotIndices = [numQubits + 1 ..]
      assignIdx [] _ = []
      assignIdx (g:gs) idxs =
        if isCNOT g then
          (g, Just (head idxs)) : assignIdx gs (tail idxs)
        else
          (g, Nothing) : assignIdx gs idxs
  in assignIdx circ cnotIndices

reorderCommuting :: [(Primitive, Maybe Int)] -> Map ID Int -> Map Vertex Block -> [(Primitive, Maybe Int)]
reorderCommuting [] _ _ = []
reorderCommuting (g:gs) qIndexMap partMap =
  case g of
    (CNOT c1 t1, Just idx1) ->
      let isSameTargetCNOT (CNOT _ t, Just _) = t == t1
          isSameTargetCNOT _ = False
          
          (block, rest) = span isSameTargetCNOT (g:gs)
          
          wPart = case Map.lookup t1 qIndexMap of
                    Just wIdx -> Map.findWithDefault 0 (Wire wIdx) partMap
                    Nothing -> -1
                    
          sortKey (_, Just idx) =
            let gPart = Map.findWithDefault 0 (GateIdx idx) partMap
            -- False < True, so local gates sort before remote gates. 
            -- 'idx' maintains the original relative order within those groups.
            in (gPart /= wPart, idx) 
            
          sortedBlock = sortBy (comparing sortKey) block
      in sortedBlock ++ reorderCommuting rest qIndexMap partMap
    _ -> g : reorderCommuting gs qIndexMap partMap


synthesizeDQC :: [(Primitive, Maybe Int)] -> Int -> Map ID Int -> Map Vertex Block -> [(Vertex, Int, Int)] -> ([Primitive], Int)
synthesizeDQC circ numQubits qIndexMap partMap boundaries =
    let 
      idxToID = Map.fromList [ (idx, qid) | (qid, idx) <- Map.toList qIndexMap ]
      
      entangleAt    = Map.fromListWith (++) [ (start, [w]) | (Wire w, start, _) <- boundaries ]
      disentangleAt = Map.fromListWith (++) [ (end, [w])   | (Wire w, _, end) <- boundaries ]

      symDiff s x = if Set.member x s then Set.delete x s else Set.insert x s

      go :: [(Primitive, Maybe Int)] -> Int -> Map Int ID -> Map Int (Set ID) -> ([Primitive], Int)
      go [] bellPairCount _ _ = 
          ([Reset ("bell" ++ show i) | i <- [0 .. (bellPairCount * 2) - 1]], bellPairCount)
          
      go ((gate, mIdx):gates) bellPairCount activeEPRs corrections =
        let
          mustFlush (w, s) = not (Set.null s) && case gate of
              CNOT _ t -> Set.member t s                     
              _        -> any (`Set.member` s) (getArgs gate) 
          
          flushTargets = [ w | (w, s) <- Map.toList corrections, mustFlush (w, s) ]
          
          (flushGates, activeEPRs_flushed, corrections_flushed, bellPairCount_flushed) = 
              foldl (applyDisentangler idxToID) ([], activeEPRs, corrections, bellPairCount) flushTargets
        in 
        if isCNOT gate then
          case mIdx of
            Just currentGateIdx ->
              let gatePart = Map.findWithDefault 0 (GateIdx currentGateIdx) partMap
                  -- 1. Apply Entanglers
                  wiresToEntangle = Map.findWithDefault [] currentGateIdx entangleAt
                  (entanglers, bellPairCount', activeEPRs', corrections') = 
                      foldl (applyEntangler idxToID) ([], bellPairCount_flushed, activeEPRs_flushed, corrections_flushed) wiresToEntangle
                  -- 2. Substitute arguments and update target correction sets
                  (gate', corrections'') = processCNOT gate activeEPRs' corrections' gatePart
                  -- 3. Apply Disentanglers
                  wiresToDisentangle = Map.findWithDefault [] currentGateIdx disentangleAt
                  (disentanglers, activeEPRs'', corrections''', bellPairCount'') = 
                      foldl (applyDisentangler idxToID) ([], activeEPRs', corrections'', bellPairCount') wiresToDisentangle
                  
                  (restCirc, finalCount) = go gates bellPairCount'' activeEPRs'' corrections'''
                  
              in (flushGates ++ entanglers ++ [gate'] ++ disentanglers ++ restCirc, finalCount)
            Nothing -> error "CNOT missing original index"
        else
          let (restCirc, finalCount) = go gates bellPairCount_flushed activeEPRs_flushed corrections_flushed
          in (flushGates ++ [gate] ++ restCirc, finalCount)

      applyEntangler mapping (accGates, pairCount, active, corr) wireIdx =
        let srcQubit = mapping Map.! wireIdx
            bell1 = "bell" ++ show (pairCount * 2)
            bell2 = "bell" ++ show (pairCount * 2 + 1)
            gates = catEntangler srcQubit bell1 bell2
        in (accGates ++ gates, pairCount + 1, Map.insert wireIdx bell1 active, Map.insert wireIdx Set.empty corr)

      processCNOT (CNOT ctrl tgt) active corr gatePart =
        let cIdxM = Map.lookup ctrl qIndexMap
            tIdxM = Map.lookup tgt qIndexMap
            actualCtrl = case cIdxM of
                Just cIdx -> 
                    let wPart = Map.findWithDefault 0 (Wire cIdx) partMap
                    in if wPart /= gatePart && Map.member cIdx active
                       then active Map.! cIdx else ctrl
                Nothing -> ctrl
            actualTgt = case tIdxM of
                Just tIdx -> 
                    let wPart = Map.findWithDefault 0 (Wire tIdx) partMap
                    in if wPart /= gatePart && Map.member tIdx active
                       then active Map.! tIdx else tgt
                Nothing -> tgt
            corr' = case tIdxM of
                Just tIdx ->
                    let wPart = Map.findWithDefault 0 (Wire tIdx) partMap
                    in if wPart /= gatePart && Map.member tIdx active  
                       then Map.adjust (\s -> symDiff s ctrl) tIdx corr
                       else corr
                Nothing -> corr
        in (CNOT actualCtrl actualTgt, corr')
      processCNOT g _ c _ = (g, c)

      applyDisentangler mapping (accGates, active, corr, pairCount) wireIdx =
        case Map.lookup wireIdx active of
          Nothing -> (accGates, active, corr, pairCount) 
          Just bell1 ->
            let srcQubit = mapping Map.! wireIdx
                s = Map.findWithDefault Set.empty wireIdx corr
            in if Set.null s
               then 
                   let gates = catDisentangler srcQubit bell1
                   in (accGates ++ gates, Map.delete wireIdx active, Map.delete wireIdx corr, pairCount)
               else 
                   let f1 = "bell" ++ show (pairCount * 2)
                       f2 = "bell" ++ show (pairCount * 2 + 1)
                       gates = targetDisentangler srcQubit bell1 f1 f2 s
                   in (accGates ++ gates, Map.delete wireIdx active, Map.delete wireIdx corr, pairCount + 1)
               
  in go circ 0 Map.empty Map.empty


buildDistributedCircuitCnotApproach :: Int -> [Primitive] -> IO [Primitive]
buildDistributedCircuitCnotApproach numParts circ = do
  (hyp, qIndexMap, _) <- HG.getNumCuts numParts circ
  
  let numQubits = Map.size qIndexMap
      partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
  partMap <- readPartitionFile partitionPath numQubits
  let boundaries = getTeleportationBoundaries hyp partMap
  
  -- Pre-processing pass: Annotate and reorder the circuit
  let annotatedCirc = annotateCircuit circ numQubits
      reorderedCirc = reorderCommuting annotatedCirc qIndexMap partMap
  
  let (distributedCirc, actualEbits) = synthesizeDQC reorderedCirc numQubits qIndexMap partMap boundaries
  putStrLn $ "# Actual ebits used (Synthesis): " ++ show actualEbits

  let getPart wIdx = 
        case Map.lookup (Wire wIdx) partMap of
          Just p  -> p
          Nothing -> error $ "FATAL: qubit " ++ show wIdx ++ " is completely missing from the partition map!"

      partitions = Map.fromList 
        [ (qid, getPart wIdx) 
        | (qid, wIdx) <- Map.toList qIndexMap 
        ]
  
--   if verifyDist distributedCirc partitions
--     then putStrLn "# Distribution Verification: PASS"
--     else putStrLn "# Distribution Verification: FAIL (cross-partition gate detected)"
  
  return distributedCirc