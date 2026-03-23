module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import Feynman.Core (Primitive(..), getArgs, ID, isCZ, isCNOT,Block, Vertex(..), Hypergraph(..), Hyperedge, substGate)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath ((</>))


initBellPairs :: ID -> ID -> [Primitive]
initBellPairs bell1 bell2 = [H bell1, CNOT bell1 bell2]

catEntangler :: ID -> ID -> ID -> [Primitive]
catEntangler srcQubit bell1 bell2 =
    initBellPairs bell1 bell2 ++ [CNOT srcQubit bell2, Measure bell2, CNOT bell2 bell1]

catDisentangler :: ID -> ID -> [Primitive]
catDisentangler srcQubit bell = [H bell,Measure bell,CZ bell srcQubit]

quasiSwap:: ID -> ID -> [Primitive]
quasiSwap qubit1 qubit2 = [CNOT qubit1 qubit2, CNOT qubit2 qubit1]

-- Phase corrections for the control sets
phaseCorrection:: ID -> Set ID -> [Primitive]
phaseCorrection ctrlQubit s = [CZ ctrlQubit c | c <- Set.toList s]

-- | Disentangles a shared target qubit using a secondary Bell pair and applies phase corrections.
-- 1. Share sA with QPU1 via new Bell pair (f1, f2)
-- 2. Quasi swap
-- 3. Disentangle and measure
-- Phase corrections for the control sets
-- Standard disentangle for the original target
targetDisentangler :: ID -> ID -> ID -> ID -> Set ID -> [Primitive]
targetDisentangler a sA f1 f2 s =
    catEntangler sA f1 f2 ++ [Reset f2] ++ quasiSwap a f1 ++ [H f1,Measure f1] ++
    phaseCorrection f1 s ++ catDisentangler a sA

-- | Read all partition lines and map them to Vertex (Wire or GateIdx)
readPartitionFile :: FilePath -> Int -> IO (Map Vertex Block)
readPartitionFile filepath numQubits = do
  contents <- readFile filepath
  let partLines = lines contents
      assignments = zip [1..] (map read partLines :: [Int])
      
      -- Convert indices back to Vertex types based on the total number of qubits
      toVertex (idx, part)
        | idx <= numQubits = (Wire idx, part)
        | otherwise        = (GateIdx idx, part)
        
  return $ Map.fromList (map toVertex assignments)

-- | Analyzes hyperedges to find where to insert entanglers and disentanglers
getTeleportationBoundaries :: Hypergraph -> Map Vertex Block -> [(Vertex, Int, Int)]
getTeleportationBoundaries (Hypergraph _ hedges) partMap = mapMaybe (analyzeEdge . fst) hedges
  where
    analyzeEdge :: Hyperedge -> Maybe (Vertex, Int, Int)
    analyzeEdge hedge = 
      let vertices = Set.toList hedge
          wires    = [w | w@(Wire _) <- vertices]
          gates    = [g | GateIdx g <- vertices]
      in case wires of
           [wire] -> 
             let wirePart = Map.findWithDefault 0 wire partMap
                 -- Find all gates in this hyperedge that are in a DIFFERENT partition than the wire
                 nonLocalGates = [ g | g <- gates
                                 , Map.findWithDefault 0 (GateIdx g) partMap /= wirePart ]
             in if null nonLocalGates
                then Nothing
                -- Start at the earliest non-local gate, but maintain the wire until the END of the hyperedge
                else Just (wire, minimum nonLocalGates, maximum gates) 
           _ -> Nothing -- Malformed hyperedge

-- | Core synthesis logic that iterates through the circuit and splices in EPR pairs
synthesizeCzDQC :: [Primitive] -> Int -> Map ID Int -> Map Vertex Block -> [(Vertex, Int, Int)] -> [Primitive]
synthesizeCzDQC circ numQubits qIndexMap partMap boundaries =
  -- Reverse map to look up ID string from Wire index
    let 
      idxToID = Map.fromList [ (idx, qid) | (qid, idx) <- Map.toList qIndexMap ]
      
      -- Pre-compute start and end maps for fast lookup: GateIdx -> [WireIdx]
      entangleAt    = Map.fromListWith (++) [ (start, [w]) | (Wire w, start, _) <- boundaries ]
      disentangleAt = Map.fromListWith (++) [ (end, [w])   | (Wire w, _, end) <- boundaries ]

      -- State-tracking loop: (Remaining Circuit) -> CZ Counter -> Bell Pair Counter -> Active Teleportations -> New Circuit
      go :: [Primitive] -> Int -> Int -> Map Int ID -> [Primitive]
      
      -- Base Case: Add reset gates for all generated bell pairs to ensure they appear in .v declarations
      go [] _ bellPairCount _ = 
          [Reset ("bell" ++ show i) | i <- [0 .. (bellPairCount * 2) - 1]]
          
      go (gate:gates) czCount bellPairCount activeEPRs =
        if isCZ gate then
          let currentGateIdx = numQubits + 1 + czCount
              gatePart = Map.findWithDefault 0 (GateIdx currentGateIdx) partMap
              
              -- 1. Check & Apply Entanglers BEFORE this gate
              wiresToEntangle = Map.findWithDefault [] currentGateIdx entangleAt
              (entanglers, bellPairCount', activeEPRs') = foldl (applyEntangler idxToID) ([], bellPairCount, activeEPRs) wiresToEntangle
              
              -- 2. Substitute arguments in the current gate using activeEPRs
              -- Only substitute if the gate's partition doesn't match the wire's native partition
              gate' = substActive activeEPRs' gatePart gate
              
              -- 3. Check & Apply Disentanglers AFTER this gate
              wiresToDisentangle = Map.findWithDefault [] currentGateIdx disentangleAt
              (disentanglers, activeEPRs'') = foldl (applyDisentangler idxToID) ([], activeEPRs') wiresToDisentangle
              
          in entanglers ++ [gate'] ++ disentanglers ++ go gates (czCount + 1) bellPairCount' activeEPRs''
        else
           -- Non-CZ gate. Leave it untouched since hyperedges break before non-diagonal gates.
          gate : go gates czCount bellPairCount activeEPRs

      applyEntangler mapping (accGates, pairCount, active) wireIdx =
        let srcQubit = mapping Map.! wireIdx
            bell1 = "bell" ++ show (pairCount * 2)
            bell2 = "bell" ++ show (pairCount * 2 + 1)
            gates = catEntangler srcQubit bell1 bell2
        in (accGates ++ gates, pairCount + 1, Map.insert wireIdx bell1 active)

      applyDisentangler mapping (accGates, active) wireIdx =
        let srcQubit = mapping Map.! wireIdx
            bell1 = active Map.! wireIdx
            gates = catDisentangler srcQubit bell1
        in (accGates ++ gates, Map.delete wireIdx active)

      -- Replace Original ID with Active EPR ID *only* if gate partition != wire partition
      substActive active gatePart g = 
        let replace q = case Map.lookup q qIndexMap of
                          Just wIdx -> 
                            let wirePart = Map.findWithDefault 0 (Wire wIdx) partMap
                            in if wirePart /= gatePart && Map.member wIdx active
                               then active Map.! wIdx
                               else q
                          Nothing   -> q
        in substGate replace g
        
  in go circ 0 0 Map.empty

synthesizeDQC :: [Primitive] -> Int -> Map ID Int -> Map Vertex Block -> [(Vertex, Int, Int)] -> ([Primitive], Int)
synthesizeDQC circ numQubits qIndexMap partMap boundaries =
    let 
      idxToID = Map.fromList [ (idx, qid) | (qid, idx) <- Map.toList qIndexMap ]
      
      entangleAt    = Map.fromListWith (++) [ (start, [w]) | (Wire w, start, _) <- boundaries ]
      disentangleAt = Map.fromListWith (++) [ (end, [w])   | (Wire w, _, end) <- boundaries ]

      symDiff s x = if Set.member x s then Set.delete x s else Set.insert x s

      -- State-tracking loop returns the circuit AND the final bell pair count
      go :: [Primitive] -> Int -> Int -> Map Int ID -> Map Int (Set ID) -> ([Primitive], Int)
      
      -- Base Case: Return the resets and the final count
      go [] _ bellPairCount _ _ = 
          ([Reset ("bell" ++ show i) | i <- [0 .. (bellPairCount * 2) - 1]], bellPairCount)
          
      go (gate:gates) cnotCount bellPairCount activeEPRs corrections =
        let
        -- SAFEGUARD: If a control is about to change basis or be targeted itself, 
        -- Force an early disentanglement to safely apply the delayed Z kickback.
          mustFlush (w, s) = not (Set.null s) && case gate of
              CNOT _ t -> Set.member t s                     
              _        -> any (`Set.member` s) (getArgs gate) 
          
          flushTargets = [ w | (w, s) <- Map.toList corrections, mustFlush (w, s) ]
          
          (flushGates, activeEPRs_flushed, corrections_flushed, bellPairCount_flushed) = 
              foldl (applyDisentangler idxToID) ([], activeEPRs, corrections, bellPairCount) flushTargets
        in 
        if isCNOT gate then
          let currentGateIdx = numQubits + 1 + cnotCount
              gatePart = Map.findWithDefault 0 (GateIdx currentGateIdx) partMap
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
              
              -- Recursively call 'go' and extract the remaining circuit and the final count
              (restCirc, finalCount) = go gates (cnotCount + 1) bellPairCount'' activeEPRs'' corrections'''
              
          in (flushGates ++ entanglers ++ [gate'] ++ disentanglers ++ restCirc, finalCount)
        else
          let (restCirc, finalCount) = go gates cnotCount bellPairCount_flushed activeEPRs_flushed corrections_flushed
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
                    if Map.member tIdx active  
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
               
  in go circ 0 0 Map.empty Map.empty


-- synthesizeDQC :: [Primitive] -> Int -> Map ID Int -> Map Vertex Block -> [(Vertex, Int, Int)] -> [Primitive]
-- synthesizeDQC circ numQubits qIndexMap partMap boundaries =
--     let 
--       idxToID = Map.fromList [ (idx, qid) | (qid, idx) <- Map.toList qIndexMap ]
      
--       entangleAt    = Map.fromListWith (++) [ (start, [w]) | (Wire w, start, _) <- boundaries ]
--       disentangleAt = Map.fromListWith (++) [ (end, [w])   | (Wire w, _, end) <- boundaries ]

--       -- Helper for symmetric difference
--       symDiff s x = if Set.member x s then Set.delete x s else Set.insert x s

--       -- State-tracking loop: 
--       -- (Remaining Circuit) -> CNOT Counter -> Bell Pair Counter -> Active Teleportations -> Target Corrections -> New Circuit
--       go :: [Primitive] -> Int -> Int -> Map Int ID -> Map Int (Set ID) -> [Primitive]
      
--       go [] _ bellPairCount _ _ = 
--           [Reset ("bell" ++ show i) | i <- [0 .. (bellPairCount * 2) - 1]]
          
--       go (gate:gates) cnotCount bellPairCount activeEPRs corrections =
--         if isCNOT gate then
--           let currentGateIdx = numQubits + 1 + cnotCount
--               gatePart = Map.findWithDefault 0 (GateIdx currentGateIdx) partMap
              
--               -- 1. Apply Entanglers
--               wiresToEntangle = Map.findWithDefault [] currentGateIdx entangleAt
--               (entanglers, bellPairCount', activeEPRs', corrections') = 
--                   foldl (applyEntangler idxToID) ([], bellPairCount, activeEPRs, corrections) wiresToEntangle
              
--               -- 2. Substitute arguments and update target correction sets
--               (gate', corrections'') = processCNOT gate activeEPRs' corrections' gatePart
              
--               -- 3. Apply Disentanglers
--               wiresToDisentangle = Map.findWithDefault [] currentGateIdx disentangleAt
--               (disentanglers, activeEPRs'', corrections''', bellPairCount'') = 
--                   foldl (applyDisentangler idxToID) ([], activeEPRs', corrections'', bellPairCount') wiresToDisentangle
              
--           in entanglers ++ [gate'] ++ disentanglers ++ go gates (cnotCount + 1) bellPairCount'' activeEPRs'' corrections'''
--         else
--           -- Leave non-CNOT gates untouched
--           gate : go gates cnotCount bellPairCount activeEPRs corrections

--       applyEntangler mapping (accGates, pairCount, active, corr) wireIdx =
--         let srcQubit = mapping Map.! wireIdx
--             bell1 = "bell" ++ show (pairCount * 2)
--             bell2 = "bell" ++ show (pairCount * 2 + 1)
--             gates = catEntangler srcQubit bell1 bell2
--         in (accGates ++ gates, pairCount + 1, Map.insert wireIdx bell1 active, Map.insert wireIdx Set.empty corr)

--       processCNOT (CNOT ctrl tgt) active corr gatePart =
--         let cIdxM = Map.lookup ctrl qIndexMap
--             tIdxM = Map.lookup tgt qIndexMap
            
--             -- actual IDs for the gate
--             actualCtrl = case cIdxM of
--                 Just cIdx -> 
--                     let wPart = Map.findWithDefault 0 (Wire cIdx) partMap
--                     in if wPart /= gatePart && Map.member cIdx active
--                        then active Map.! cIdx else ctrl
--                 Nothing -> ctrl
                
--             actualTgt = case tIdxM of
--                 Just tIdx -> 
--                     let wPart = Map.findWithDefault 0 (Wire tIdx) partMap
--                     in if wPart /= gatePart && Map.member tIdx active
--                        then active Map.! tIdx else tgt
--                 Nothing -> tgt
                
--             -- Update correction set S = S \oplus {B} if target is actively shared
--             corr' = case tIdxM of
--                 Just tIdx ->
--                     if Map.member tIdx active
--                        then Map.adjust (\s -> symDiff s ctrl) tIdx corr
--                        else corr
--                 Nothing -> corr
                
--         in (CNOT actualCtrl actualTgt, corr')
--       processCNOT g _ c _ = (g, c)

--       applyDisentangler mapping (accGates, active, corr, pairCount) wireIdx =
--         let srcQubit = mapping Map.! wireIdx
--             bell1 = active Map.! wireIdx
--             s = Map.findWithDefault Set.empty wireIdx corr
--         in if Set.null s
--            then 
--                -- Was only used as a control, standard disentanglement
--                let gates = catDisentangler srcQubit bell1
--                in (accGates ++ gates, Map.delete wireIdx active, Map.delete wireIdx corr, pairCount)
--            else 
--                -- Was used as a target, requires phase corrections via new Bell pair
--                let f1 = "bell" ++ show (pairCount * 2)
--                    f2 = "bell" ++ show (pairCount * 2 + 1)
--                    gates = targetDisentangler srcQubit bell1 f1 f2 s
--                in (accGates ++ gates, Map.delete wireIdx active, Map.delete wireIdx corr, pairCount + 1)
               
--   in go circ 0 0 Map.empty Map.empty

buildDistributedCircuit :: [Primitive] -> IO [Primitive]
buildDistributedCircuit circ = do
  -- Extract hypergraph, index map, and circuit
  (hyp, qIndexMap, _) <- HG.getNumCuts circ
  
  let numQubits = Map.size qIndexMap
      partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
  partMap <- readPartitionFile partitionPath numQubits
  let boundaries = getTeleportationBoundaries hyp partMap
  
  -- Unpack the tuple to get the circuit and the actual ebits used
  let (distributedCirc, actualEbits) = synthesizeDQC circ numQubits qIndexMap partMap boundaries
  putStrLn $ "# Actual ebits used (Synthesis): " ++ show actualEbits

--   let distributedCirc  = synthesizeDQC circ numQubits qIndexMap partMap boundaries
  
  return distributedCirc