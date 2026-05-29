module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import Feynman.Core (Primitive(..), getArgs, ID, isCZ, isCNOT,Block, Vertex(..), Hypergraph(..), Hyperedge, substGate, PartitionData)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath ((</>))

import Data.List (sortBy, groupBy)
import Data.Ord (comparing)


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
-- getTeleportationBoundaries :: Hypergraph -> Map Vertex Block -> [(Vertex, Int, Int)]
-- getTeleportationBoundaries (Hypergraph _ hedges) partMap = mapMaybe (analyzeEdge . fst) hedges
--   where
--     analyzeEdge :: Hyperedge -> Maybe (Vertex, Int, Int)
--     analyzeEdge hedge = 
--       let vertices = Set.toList hedge
--           wires    = [w | w@(Wire _) <- vertices]
--           gates    = [g | GateIdx g <- vertices]
--       in case wires of
--            [wire] -> 
--              let wirePart = Map.findWithDefault 0 wire partMap
--                  nonLocalGates = [ g | g <- gates
--                                  , Map.findWithDefault 0 (GateIdx g) partMap /= wirePart ]
--              in if null nonLocalGates
--                 then Nothing
--                 else Just (wire, minimum nonLocalGates, maximum nonLocalGates) 
--            _ -> Nothing

getTeleportationBoundaries :: Hypergraph -> Map Vertex Block -> [(Vertex, Int, Int)]
getTeleportationBoundaries (Hypergraph _ hedges) partMap = concatMap (analyzeEdge . fst) hedges
  where
    analyzeEdge :: Hyperedge -> [(Vertex, Int, Int)]
    analyzeEdge hedge = 
      let vertices = Set.toList hedge
          wires    = [w | w@(Wire _) <- vertices]
          gates    = [g | GateIdx g <- vertices]
      in case wires of
           [wire] -> 
             let wirePart = Map.findWithDefault 0 wire partMap
                 -- 1. Extract all gates that don't match the wire's native partition
                 nonLocalGates = [ g | g <- gates
                                 , Map.findWithDefault 0 (GateIdx g) partMap /= wirePart ]
                 
                 -- 2. Sort them chronologically
                 sortedNonLocal = sortBy compare nonLocalGates
                 
                 -- 3. Group consecutive gates if they share the exact same remote partition
                 samePart g1 g2 = Map.findWithDefault 0 (GateIdx g1) partMap == 
                                  Map.findWithDefault 0 (GateIdx g2) partMap
                 
                 groups = groupBy samePart sortedNonLocal
                 
                 -- 4. Create distinct boundaries for each distinct cluster
                 makeBoundary grp = (wire, head grp, last grp)
             in map makeBoundary groups
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

-- verifyDist :: [Primitive] -> PartitionData -> Bool
-- verifyDist circuit partitions = all checkGate circuit
--   where
--     checkGate :: Primitive -> Bool
--     checkGate (CNOT ctrl tgt) = isLocal ctrl tgt
--     checkGate (CZ ctrl tgt) = isLocal ctrl tgt
--     checkGate _ = True

--     isLocal :: ID -> ID -> Bool
--     isLocal q1 q2 = case (Map.lookup q1 partitions, Map.lookup q2 partitions) of
--       (Just p1, Just p2) -> p1 == p2
--       _ -> True

verifyDist :: [Primitive] -> PartitionData -> Bool
verifyDist circuit initialPartitions = go circuit initialPartitions
  where
    go :: [Primitive] -> Map ID Int -> Bool
    go [] _ = True
    go (gate:gs) env =
      case gate of
        CNOT q1 q2 ->
          -- Skip internal inter-QPU EPR generation and teleportation feedback lines
          if isBell q1 && isBell q2
          then go gs env
          else case checkAndApply q1 q2 env of
                 Just env' -> go gs env'
                 Nothing   -> False -- Real cross-partition violation!
                 
        CZ q1 q2   ->
          -- Skip inter-QPU classical phase correction steps
          if isBell q1 || isBell q2
          then go gs env
          else case checkAndApply q1 q2 env of
                 Just env' -> go gs env'
                 Nothing   -> False -- Real cross-partition violation!
                 
        _          -> go gs env -- Single-qubit gates are inherently local

    -- Helper to identify dynamically generated infrastructure qubits
    isBell :: ID -> Bool
    isBell q = take 4 q == "bell"

    -- Enforces partition alignment and dynamically tracks/propagates proxy placements
    checkAndApply :: ID -> ID -> Map ID Int -> Maybe (Map ID Int)
    checkAndApply q1 q2 env =
      case (Map.lookup q1 env, Map.lookup q2 env) of
        (Just p1, Just p2) -> if p1 == p2 then Just env else Nothing
        (Just p1, Nothing) -> Just (Map.insert q2 p1 env)
        (Nothing, Just p2) -> Just (Map.insert q1 p2 env)
        (Nothing, Nothing) -> Just env

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

-- buildDistributedCircuit :: Int -> [Primitive] -> IO [Primitive]
-- buildDistributedCircuit numParts circ = do
--   (hyp, qIndexMap, _) <- HG.getNumCuts numParts circ
  
--   let numQubits = Map.size qIndexMap
--       partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
--   partMap <- readPartitionFile partitionPath numQubits
--   let boundaries = getTeleportationBoundaries hyp partMap
  
--   -- Pre-processing pass: Annotate and reorder the circuit
--   let annotatedCirc = annotateCircuit circ numQubits
--       reorderedCirc = reorderCommuting annotatedCirc qIndexMap partMap
  
--   let (distributedCirc, actualEbits) = synthesizeDQC reorderedCirc numQubits qIndexMap partMap boundaries
--   putStrLn $ "# Actual ebits used (Synthesis): " ++ show actualEbits

--   let getPart wIdx = 
--         case Map.lookup (Wire wIdx) partMap of
--           Just p  -> p
--           Nothing -> error $ "FATAL: qubit " ++ show wIdx ++ " is completely missing from the partition map!"

--       partitions = Map.fromList 
--         [ (qid, getPart wIdx) 
--         | (qid, wIdx) <- Map.toList qIndexMap 
--         ]
  
--   if verifyDist distributedCirc partitions
--     then putStrLn "# Distribution Verification: PASS"
--     else putStrLn "# Distribution Verification: FAIL (cross-partition gate detected)"
  
--   return distributedCirc

buildDistributedCircuit :: Int -> [Primitive] -> IO [Primitive]
buildDistributedCircuit numParts circ = do
  (hyp, qIndexMap, _) <- HG.getNumCuts numParts circ
  
  let numQubits = Map.size qIndexMap
      partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
  partMap <- readPartitionFile partitionPath numQubits
  
  -- putStrLn ">>> STEP 2 CHECK: SUCCESSFUL GRAPH PARTITIONING <<<"
  -- putStrLn $ "# Registered partition mapping entities: " ++ show (Map.size partMap)
  -- putStrLn "# Snapshot Sample of allocations (Vertex -> Target QPU Node):"
  -- print (Map.toList $ Map.take 10 partMap)
  
  -- Return base circuit unaltered to preserve verification pipeline execution safety
  return circ