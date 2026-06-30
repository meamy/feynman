module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where

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

import Data.List (sortBy, groupBy, foldl')
import Data.Ord (comparing)

import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict (runState)
import Control.Monad (foldM)

import Debug.Trace (trace)

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

-- getTeleportationBoundaries :: Hypergraph -> Map Vertex Block -> [(Vertex, Int, Int)]
-- getTeleportationBoundaries (Hypergraph _ hedges) partMap = concatMap (analyzeEdge . fst) hedges
--   where
--     analyzeEdge :: Hyperedge -> [(Vertex, Int, Int)]
--     analyzeEdge hedge = 
--       let vertices = Set.toList hedge
--           wires    = [w | w@(Wire _) <- vertices]
--           gates    = [g | GateIdx g <- vertices]
--       in case wires of
--            [wire] -> 
--              let wirePart = Map.findWithDefault 0 wire partMap
--                  -- 1. Extract all gates that don't match the wire's native partition
--                  nonLocalGates = [ g | g <- gates
--                                  , Map.findWithDefault 0 (GateIdx g) partMap /= wirePart ]
                 
--                  -- 2. Sort them chronologically
--                  sortedNonLocal = sortBy compare nonLocalGates
                 
--                  -- 3. Group consecutive gates if they share the exact same remote partition
--                  samePart g1 g2 = Map.findWithDefault 0 (GateIdx g1) partMap == 
--                                   Map.findWithDefault 0 (GateIdx g2) partMap
                 
--                  groups = groupBy samePart sortedNonLocal
                 
--                  -- 4. Create distinct boundaries for each distinct cluster
--                  makeBoundary grp = (wire, head grp, last grp)
--              in map makeBoundary groups
--            _ -> []

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

-- verifyDist :: [Primitive] -> PartitionData -> Bool
-- verifyDist circuit initialPartitions = go circuit initialPartitions
--   where
--     go :: [Primitive] -> Map ID Int -> Bool
--     go [] _ = True
--     go (gate:gs) env =
--       case gate of
--         CNOT q1 q2 ->
--           -- Skip internal inter-QPU EPR generation and teleportation feedback lines
--           if isBell q1 && isBell q2
--           then go gs env
--           else case checkAndApply q1 q2 env of
--                  Just env' -> go gs env'
--                  Nothing   -> False -- Real cross-partition violation!
                 
--         CZ q1 q2   ->
--           -- Skip inter-QPU classical phase correction steps
--           if isBell q1 || isBell q2
--           then go gs env
--           else case checkAndApply q1 q2 env of
--                  Just env' -> go gs env'
--                  Nothing   -> False -- Real cross-partition violation!
                 
--         _          -> go gs env -- Single-qubit gates are inherently local

--     -- Helper to identify dynamically generated infrastructure qubits
--     isBell :: ID -> Bool
--     isBell q = take 4 q == "bell"

--     -- Enforces partition alignment and dynamically tracks/propagates proxy placements
--     checkAndApply :: ID -> ID -> Map ID Int -> Maybe (Map ID Int)
--     checkAndApply q1 q2 env =
--       case (Map.lookup q1 env, Map.lookup q2 env) of
--         (Just p1, Just p2) -> if p1 == p2 then Just env else Nothing
--         (Just p1, Nothing) -> Just (Map.insert q2 p1 env)
--         (Nothing, Just p2) -> Just (Map.insert q1 p2 env)
--         (Nothing, Nothing) -> Just env


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
                 
        Reset q    -> 
          -- FREE THE QUBIT: Allow Bell proxy IDs to be reused in the next chunk
          go gs (Map.delete q env)
                 
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

-- -- Old approach
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

rankFactorization :: F2Mat -> (F2Mat, F2Mat)
rankFactorization a
  | m a > n a = let (f, c) = rankFactorization (transpose a)
                in  (transpose c, transpose f)
  | otherwise =
      -- FIX: We MUST use toReducedEchelon so that A = C * F mathematically holds.
      let ref       = fst . runWriter . toReducedEchelon $ a   
          pivots    = findPivots ref
          aT        = transpose a
          cT        = fromList [ row aT p | p <- pivots ] -- pivot COLUMNS of original
          f         = fromList [ row ref i | i <- [0 .. length pivots - 1] ]
      in  (transpose cT, f)   -- C is m×r, F is r×n

-- Helper: find the column index of each pivot in row echelon form
findPivots :: F2Mat -> [Int]
findPivots mat = go 0 0
  where
    go i j | i >= m mat || j >= n mat = []
           | row mat i @. j            = j : go (i+1) (j+1)
           | otherwise                 = go i (j+1)

synthSplitRank :: [ID] -> F2Mat -> Int -> Bool -> [Primitive]
synthSplitRank ids b n down
  | m b == 0 || Feynman.Algebra.Linear.n b == 0 = []   -- empty biadjacency: nothing to do
  | otherwise = concatMap synthTerm (zip (toList (transpose c)) (toList f))
  where
    (c, f) = rankFactorization b
    numRowsB = m b   -- number of rows of B = size of first group involved
    numColsB = Feynman.Algebra.Linear.n b  -- number of cols of B = size of second group

    synthTerm (u, v) =
      let ii = lsb1 u
          jj = lsb1 v
          -- u has width numRowsB, index into ids directly (these are group-0 local indices)
          fanU = [ if down then CNOT (ids !! k)       (ids !! ii)
                           else CNOT (ids !! ii)      (ids !! k)
                 | k <- [0 .. numRowsB - 1], u @. k, k /= ii ]
          -- v has width numColsB, offset by n into ids
          fanV = [ if down then CNOT (ids !! (jj+n))  (ids !! (k+n))
                           else CNOT (ids !! (k+n))   (ids !! (jj+n))
                 | k <- [0 .. numColsB - 1], v @. k, k /= jj ]
          prep  = fanU ++ fanV
          cross = if down then CNOT (ids !! ii)       (ids !! (jj+n))
                          else CNOT (ids !! (jj+n))   (ids !! ii)
      in  prep ++ [cross] ++ reverse prep


blockLduFact :: F2Mat -> Int -> (F2Mat, F2Mat, F2Mat)
blockLduFact mat n =
  let sz   = m mat
      m'   = sz - n
      a    = subMat mat (0, n)  (0, n)   -- top-left     n×n
      b    = subMat mat (0, n)  (n, sz)  -- top-right    n×m'
      c    = subMat mat (n, sz) (0, n)   -- bottom-left  m'×n
      d    = subMat mat (n, sz) (n, sz)  -- bottom-right m'×m'
      ainv = pseudoinverse a             -- n×n (true inverse since a is invertible)
      -- Schur complement of a in mat:
      schur = add d (mult (mult c ainv) b)  -- m'×m'  (subtraction = addition in GF(2))
      -- Block-assemble L, D, U:
      idn  = identity n
      idm  = identity m'
      zero_nm = F2Mat n  m' (replicate n  (bitVec m' 0))
      zero_mn = F2Mat m' n  (replicate m' (bitVec n  0))
      l    = stackMat (    idn `hcat` zero_nm   )
                      (mult c ainv `hcat` idm   )
      d'   = stackMat (    a       `hcat` zero_nm)
                      (   zero_mn  `hcat` schur  )
      u    = stackMat (    idn     `hcat` mult ainv b)
                      (   zero_mn  `hcat` idm        )
  in  (l, d', u)

-- Horizontal concatenation helper (same number of rows)
hcat :: F2Mat -> F2Mat -> F2Mat
hcat a b = transpose $ stackMat (transpose a) (transpose b)

makeUlInv :: F2Mat -> Int -> (F2Mat, F2Mat)
makeUlInv a n
  | rank (subMat a (0, n) (0, n)) == n = (identity (m a), a)
  | otherwise =
      let sz    = m a
          -- Column echelon of the left half: rows are [0..sz), cols are [0..n)
          -- Transposing gives us a matrix whose row echelon reveals pivot *rows* of A
          leftHalf = subMat a (0, sz) (0, n)
          ref      = fst . runWriter . toEchelon . transpose $ leftHalf
          -- pivots are column indices of ref = row indices of leftHalf = row indices of A
          pivots   = findPivots ref
          -- which of those pivot rows are in the upper block vs lower block
          upperPivots  = filter (<  n) pivots
          lowerPivots  = filter (>= n) pivots
          -- upper rows that are NOT pivots (need to be fixed)
          upperNonPivs = filter (`notElem` upperPivots) [0..n-1]
          -- pair each deficient upper row with a lower pivot row to borrow from
          pairs        = zip upperNonPivs lowerPivots
          applyPair (u, r) (i, j) = (addRow j i u, addRow j i r)
          (u, r)       = foldl' applyPair (identity sz, a) pairs
      in  (u, r)

blockUlduFact :: F2Mat -> Int -> (F2Mat, F2Mat, F2Mat, F2Mat)
blockUlduFact a n =
  let (u, r)    = makeUlInv a n
      (l, d, u2) = blockLduFact r n
  in  (u, l, d, u2)

synthDistributed :: [ID] -> F2Mat -> Int -> [Primitive]
synthDistributed ids a n =
  let sz        = m a
      (u, l, d, u2) = blockUlduFact a n
      -- Biadjacency blocks:
      uBlock    = subMat u  (0, n)  (n, sz)
      lBlock    = subMat l  (n, sz) (0, n)
      d0        = subMat d  (0, n)  (0, n)
      d1        = subMat d  (n, sz) (n, sz)
      u2Block   = subMat u2 (0, n)  (n, sz)
      
      -- Local synthesis via existing linearSynth
      ids0      = take n ids
      ids1      = drop n ids
      toTrans xs = Map.fromList $ zip xs (toList . identity . length $ xs)
      synthLocal blk localIds =
        let target = Map.fromList $ zip localIds (toList blk)
        in  linearSynth (toTrans localIds) target
        
      -- Gate groups in order:
      gatesU    = synthSplitRank ids uBlock  n False
      gatesL    = synthSplitRank ids (transpose lBlock) n True
      gatesD0   = synthLocal d0 ids0
      gatesD1   = synthLocal d1 ids1
      gatesU2   = synthSplitRank ids u2Block n False
      
  -- FIX: Reverse the order so the overall parity resolves to U * L * D * U2
  in  gatesU2 ++ gatesD0 ++ gatesD1 ++ gatesL ++ gatesU

-- Shift qubit indices for group-1 local gates (already using ID list so this may be a no-op)
reindex :: Int -> Primitive -> Primitive
reindex n (CNOT c t) = CNOT c t  -- IDs already correct since we pass ids1
reindex _ g = g

-- buildPartitionMasks :: [ID] -> Map Vertex Block -> (F2Vec, F2Vec)
-- buildPartitionMasks qubits partMap =
--   let n = length qubits
--       getPart idx = Map.findWithDefault 0 (Wire idx) partMap

--       isQPU0 = reverse [ getPart i == 0 | i <- [1..n] ]
--       isQPU1 = reverse [ getPart i == 1 | i <- [1..n] ]

--   in (fromBits isQPU0, fromBits isQPU1)

-- separateParities :: [F2Vec] -> Int -> Map Vertex Block -> ([F2Vec], [F2Vec])
-- separateParities parities numQubits partMap =
--   let
--     getParityBlock j = Map.findWithDefault 0 (GateIdx (numQubits + 1 + j)) partMap

--     -- Parities assigned to QPU 0
--     s0 = [ p | (p, j) <- zip parities [0..], getParityBlock j == 0 ]
    
--     -- Parities assigned to QPU 1
--     s1 = [ p | (p, j) <- zip parities [0..], getParityBlock j == 1 ]
--   in
--     (s0, s1)

buildPartitionMasks :: [ID] -> Map ID Int -> Map Vertex Block -> (F2Vec, F2Vec)
buildPartitionMasks qubits qIndexMap partMap =
  let getPart q = case Map.lookup q qIndexMap of
                    Just wIdx -> Map.findWithDefault 0 (Wire wIdx) partMap
                    Nothing   -> 0

      isQPU0 = reverse [ getPart q == 0 | q <- qubits ]
      isQPU1 = reverse [ getPart q == 1 | q <- qubits ]

  in (fromBits isQPU0, fromBits isQPU1)

projectParities :: [F2Vec] -> F2Vec -> [F2Vec]
projectParities parities mask = map (* mask) parities

basisOfProjection :: [F2Vec] -> F2Vec -> [F2Vec]
basisOfProjection parities mask = findBasis (projectParities parities mask)


rewriteParities :: [F2Vec] -> F2Vec -> F2Vec -> ([(F2Vec, F2Vec)], F2Mat)
rewriteParities s localMask remoteMask =
  let localParts              = projectParities s localMask
      projMat                 = fromList (projectParities s remoteMask)
      (cMat, fMat)            = rankFactorization projMat
      basisCombinations       =  if m cMat == 0
                                then replicate (length s ) (fromBits []) 
                                else toList cMat

  in  if length localParts /= length basisCombinations
      then error "rewriteParities: s and cMat row count mismatch"
      else (zip localParts basisCombinations, fMat)  

synthesizeDistributedCNOT :: [ID] -> [Primitive] -> Int -> [Primitive]
synthesizeDistributedCNOT ids igates n =
  let a     = toParity ids igates
      gates = synthDistributed ids a n
      b     = toParity ids gates
  in  if a /= b
        then error "synthesizeDistributedCNOT: circuits not equivalent"
        else gates

-- synthPhases phases =
-- QPU0 stage
-- let S0 = phases on QPU0
-- let B0 = basis of project of S0 onto QPU1
-- cat-entangler
-- b0 -> QPU0
-- cnotmingrayPointed...

--cat-distangler

-- QPU1 stage
-- Similar steps like above

-- distSynth :: F2Mat -> [([Phase], [F2Vec])] -> [Primitive]
-- distSynth F2Mat phases = synthPhases phases ++ synthDistributed

-- synthPhases :: [ID] -> Int -> [Phase] -> Map Vertex Block -> [Primitive]
-- synthPhases ids numQpu0 phases partMap =
--   let
--       (mask0, mask1) = buildPartitionMasks ids partMap
--       parities = map fst phases
--       (s0_parities, s1_parities) = separateParities parities numQpu0 partMap


--       (rewrittenS0, basisF0) = rewriteParities s0_parities mask0 mask1
--       fRows0    = toList basisF0
--       numBells0 = length fRows0
      
--       -- CHANGED: Removed underscore, using "bellA" for QPU 0
--       bellIds0  = ["bellA" ++ show (i * 2) | i <- [0 .. numBells0 - 1]]

--       -- 1. Cat-Entanglers (Computed on QPU 1, sent to QPU 0)
--       entanglers0 = concat $ do
--             (i, row) <- zip [0..] fRows0
--             let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
--                 -- CHANGED: Removed underscore
--                 bell1 = "bellA" ++ show (i * 2)
--                 bell2 = "bellA" ++ show (i * 2 + 1)
--             return $ catEntanglerMulti activeSrcs bell1 bell2

--       -- 2. Setup Gray Synthesis for QPU 0
--       localIds0 = take numQpu0 ids ++ bellIds0
--       n0 = length localIds0
--       initialState0 = Map.fromList $ zip localIds0 [bitI n0 i | i <- [0 .. n0 - 1]]

--       phasesForGray0 = do
--             (s0_orig, (localP, basisP)) <- zip s0_parities rewrittenS0
--             -- Extract only the local physical bits (0 to numQpu0 - 1)
--             let localBits = [ localP @. j | j <- [0 .. numQpu0 - 1] ]
--             -- Extract the incoming basis bits
--                 basisBits = [ basisP @. j | j <- [0 .. numBells0 - 1] ]
--             -- Combine them into a target vector for Gray.hs
--                 targetVec = fromBits (localBits ++ basisBits)
--                 angle = case lookup s0_orig phases of
--                           Just ang -> ang
--                           Nothing  -> error "Phase lost mapping S0"
--             return (targetVec, angle)

--       -- 3. Execute Gray Synthesis (input state == output state to force uncomputation)
--       (grayGates0, _) = Gray.cnotMinGrayPointed initialState0 initialState0 phasesForGray0 []

--       -- 4. Cat-Disentanglers
--       disentanglers0 = concat $ do
--             (i, row) <- zip [0..] fRows0
--             let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
--                 -- CHANGED: Removed underscore
--                 bell1 = "bellA" ++ show (i * 2)
--             return $ catDisentanglerMulti activeSrcs bell1

--       (rewrittenS1, basisF1) = rewriteParities s1_parities mask1 mask0
--       fRows1    = toList basisF1
--       numBells1 = length fRows1
      
--       -- CHANGED: Removed underscore, using "bellB" for QPU 1
--       bellIds1  = ["bellB" ++ show (i * 2) | i <- [0 .. numBells1 - 1]]

--       -- 1. Cat-Entanglers (Computed on QPU 0, sent to QPU 1)
--       entanglers1 = concat $ do
--             (i, row) <- zip [0..] fRows1
--             let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
--                 -- CHANGED: Removed underscore
--                 bell1 = "bellB" ++ show (i * 2)
--                 bell2 = "bellB" ++ show (i * 2 + 1)
--             return $ catEntanglerMulti activeSrcs bell1 bell2

--       -- 2. Setup Gray Synthesis for QPU 1
--       localIds1 = drop numQpu0 ids ++ bellIds1
--       n1 = length localIds1
--       initialState1 = Map.fromList $ zip localIds1 [bitI n1 i | i <- [0 .. n1 - 1]]

--       phasesForGray1 = do
--             (s1_orig, (localP, basisP)) <- zip s1_parities rewrittenS1
--             -- Extract only the local physical bits for QPU1 (numQpu0 to end)
--             let localBits = [ localP @. j | j <- [numQpu0 .. length ids - 1] ]
--                 basisBits = [ basisP @. j | j <- [0 .. numBells1 - 1] ]
--                 targetVec = fromBits (localBits ++ basisBits)
--                 angle = case lookup s1_orig phases of
--                           Just ang -> ang
--                           Nothing  -> error "Phase lost mapping S1"
--             return (targetVec, angle)

--       -- 3. Execute Gray Synthesis
--       (grayGates1, _) = Gray.cnotMinGrayPointed initialState1 initialState1 phasesForGray1 []

--       -- 4. Cat-Disentanglers
--       disentanglers1 = concat $ do
--             (i, row) <- zip [0..] fRows1
--             let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
--                 -- CHANGED: Removed underscore
--                 bell1 = "bellB" ++ show (i * 2)
--             return $ catDisentanglerMulti activeSrcs bell1
      
--       debugMsg = unlines
--         [ "\n=== DEBUG: synthPhases Execution ==="
--         , "Qubits: " ++ show ids
--         , "Mask QPU0: " ++ show mask0
--         , "Mask QPU1: " ++ show mask1
--         , "S_0 (Assigned to QPU0): " ++ show s0_parities
--         , "S_1 (Assigned to QPU1): " ++ show s1_parities
--         , "\n--- QPU 0 Stage ---"
--         , "Basis F0 (QPU 1 must compute and send):\n" ++ show basisF0
--         -- We calculate the sorted keys inline here to avoid scope errors!
--         , "Initial State keys (Sorted IDs): " ++ show (map fst (Map.toList initialState0))
--         , "Phases mapped for Gray 0 (Target Vec, Angle): " ++ show phasesForGray0
--         , "\n--- QPU 1 Stage ---"
--         , "Basis F1 (QPU 0 must compute and send):\n" ++ show basisF1
--         -- Same inline calculation for QPU 1
--         , "Initial State keys (Sorted IDs): " ++ show (map fst (Map.toList initialState1))
--         , "Phases mapped for Gray 1 (Target Vec, Angle): " ++ show phasesForGray1
--         , "======================================\n"
--         ]

--   in
--       trace debugMsg $
--       entanglers0 ++ grayGates0 ++ disentanglers0 ++ 
--       entanglers1 ++ grayGates1 ++ disentanglers1


synthPhases :: [ID] -> Int -> [Phase] -> Map F2Vec Int -> Map ID Int -> Map Vertex Block -> ([Primitive], [ID])
synthPhases ids numQpu0 phases parityToPart qIndexMap partMap =
  let
      n = length ids
      (mask0, mask1) = buildPartitionMasks ids qIndexMap partMap
      parities = map fst phases
      
      -- Safely partition parities using the translated KaHyPar assignment
      s0_parities = [ p | p <- parities, Map.findWithDefault 0 p parityToPart == 0 ]
      s1_parities = [ p | p <- parities, Map.findWithDefault 0 p parityToPart == 1 ]

      (rewrittenS0, basisF0) = rewriteParities s0_parities mask0 mask1
      fRows0    = toList basisF0
      numBells0 = length fRows0
      
      bellIds0  = ["bellA" ++ show (i * 2) | i <- [0 .. numBells0 - 1]]
      -- Track all generated Bell pair IDs for QPU 0
      allBells0 = ["bellA" ++ show j | j <- [0 .. (numBells0 * 2) - 1]]

      -- 1. Cat-Entanglers (Computed on QPU 1, sent to QPU 0)
      entanglers0 = concat $ do
            (i, row) <- zip [0..] fRows0
            let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
                bell1 = "bellA" ++ show (i * 2)
                bell2 = "bellA" ++ show (i * 2 + 1)
            return $ catEntanglerMulti activeSrcs bell1 bell2

      -- 2. Setup Gray Synthesis for QPU 0
      localIds0 = take numQpu0 ids ++ bellIds0
      n0 = length localIds0
      initialState0 = Map.fromList $ zip localIds0 [bitI n0 i | i <- [0 .. n0 - 1]]

      phasesForGray0 = do
            (s0_orig, (localP, basisP)) <- zip s0_parities rewrittenS0
            let localBits = [ localP @. j | j <- [0 .. numQpu0 - 1] ]
                basisBits = [ basisP @. j | j <- [0 .. numBells0 - 1] ]
                -- FIX: Reverse bits before passing to fromBits so LSB maps correctly
                targetVec = fromBits (reverse (localBits ++ basisBits))
                angle = case lookup s0_orig phases of
                          Just ang -> ang
                          Nothing  -> error "Phase lost mapping S0"
            return (targetVec, angle)

      -- 3. Execute Gray Synthesis (input state == output state to force uncomputation)
      (grayGates0, _) = Gray.cnotMinGrayPointed initialState0 initialState0 phasesForGray0 []

      -- 4. Cat-Disentanglers
      disentanglers0 = concat $ do
            (i, row) <- zip [0..] fRows0
            let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
                bell1 = "bellA" ++ show (i * 2)
            return $ catDisentanglerMulti activeSrcs bell1

      (rewrittenS1, basisF1) = rewriteParities s1_parities mask1 mask0
      fRows1    = toList basisF1
      numBells1 = length fRows1
      
      bellIds1  = ["bellB" ++ show (i * 2) | i <- [0 .. numBells1 - 1]]
      -- Track all generated Bell pair IDs for QPU 1
      allBells1 = ["bellB" ++ show j | j <- [0 .. (numBells1 * 2) - 1]]

      -- 1. Cat-Entanglers (Computed on QPU 0, sent to QPU 1)
      entanglers1 = concat $ do
            (i, row) <- zip [0..] fRows1
            let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
                bell1 = "bellB" ++ show (i * 2)
                bell2 = "bellB" ++ show (i * 2 + 1)
            return $ catEntanglerMulti activeSrcs bell1 bell2

      -- 2. Setup Gray Synthesis for QPU 1
      localIds1 = drop numQpu0 ids ++ bellIds1
      n1 = length localIds1
      initialState1 = Map.fromList $ zip localIds1 [bitI n1 i | i <- [0 .. n1 - 1]]

      phasesForGray1 = do
            (s1_orig, (localP, basisP)) <- zip s1_parities rewrittenS1
            let localBits = [ localP @. j | j <- [numQpu0 .. length ids - 1] ]
                basisBits = [ basisP @. j | j <- [0 .. numBells1 - 1] ]
                -- FIX: Reverse bits before passing to fromBits so LSB maps correctly
                targetVec = fromBits (reverse (localBits ++ basisBits))
                angle = case lookup s1_orig phases of
                          Just ang -> ang
                          Nothing  -> error "Phase lost mapping S1"
            return (targetVec, angle)

      -- 3. Execute Gray Synthesis
      (grayGates1, _) = Gray.cnotMinGrayPointed initialState1 initialState1 phasesForGray1 []

      -- 4. Cat-Disentanglers
      disentanglers1 = concat $ do
            (i, row) <- zip [0..] fRows1
            let activeSrcs = [ ids !! j | j <- [0 .. length ids - 1], row @. j ]
                bell1 = "bellB" ++ show (i * 2)
            return $ catDisentanglerMulti activeSrcs bell1
            
      -- debugMsg = unlines
      --   [ "\n=== DEBUG: synthPhases Execution ==="
      --   , "Qubits (Sorted): " ++ show ids
      --   , "Mask QPU0: " ++ show mask0
      --   , "Mask QPU1: " ++ show mask1
      --   , "S_0 (Assigned to QPU0): " ++ show s0_parities
      --   , "S_1 (Assigned to QPU1): " ++ show s1_parities
      --   , "\n--- QPU 0 Stage ---"
      --   , "Basis F0 (QPU 1 must compute and send):\n" ++ show basisF0
      --   , "Initial State keys (Sorted IDs): " ++ show (map fst (Map.toList initialState0))
      --   , "Phases mapped for Gray 0 (Target Vec, Angle): " ++ show phasesForGray0
      --   , "\n--- QPU 1 Stage ---"
      --   , "Basis F1 (QPU 0 must compute and send):\n" ++ show basisF1
      --   , "Initial State keys (Sorted IDs): " ++ show (map fst (Map.toList initialState1))
      --   , "Phases mapped for Gray 1 (Target Vec, Angle): " ++ show phasesForGray1
      --   , "======================================\n"
      --   ]

  in
      -- trace debugMsg 
      ( entanglers0 ++ grayGates0 ++ disentanglers0 ++ 
        entanglers1 ++ grayGates1 ++ disentanglers1
      , allBells0 ++ allBells1
      )

-- distSynth :: [ID] -> F2Mat -> Int -> [Phase] -> Map Vertex Block -> [Primitive]
-- distSynth ids finalMat numQPUs phases partMap =
--   let
--     phaseGates = synthPhases ids numQPUs phases partMap
--     linearGates = synthDistributed ids finalMat numQPUs

--   in
--     phaseGates ++ linearGates


-- | Intercepts cross-partition CNOTs and routes them using Bell pair teleportation
routeLinearGates :: [Primitive] -> Int -> Map ID Int -> ([Primitive], [ID])
routeLinearGates circ startBell env = go circ startBell []
  where
    go [] _ accBells = ([], accBells)
    go (CNOT c t : gs) bellCount accBells =
      let pC = Map.findWithDefault 0 c env
          pT = Map.findWithDefault 0 t env
      in if pC /= pT
         then
           -- Route using 1 Bell pair proxy
           let b1 = "bellL" ++ show (bellCount * 2)
               b2 = "bellL" ++ show (bellCount * 2 + 1)
               proxyGates = catEntangler c b1 b2 ++ [CNOT b1 t] ++ catDisentangler c b1
               (rest, bells) = go gs (bellCount + 1) (b1 : b2 : accBells)
           in (proxyGates ++ rest, bells)
         else
           let (rest, bells) = go gs bellCount accBells
           in (CNOT c t : rest, bells)
    go (g:gs) bellCount accBells =
      let (rest, bells) = go gs bellCount accBells
      in (g : rest, bells)

-- distSynth :: [ID] -> F2Mat -> Int -> [Phase] -> Map F2Vec Int -> Map ID Int -> Map Vertex Block -> [Primitive]
-- distSynth ids finalMat numQPUs phases parityToPart qIndexMap partMap =
--   let
--     -- Unpack the gates and the dynamic bell pair names
--     (phaseGates, generatedBells) = synthPhases ids numQPUs phases parityToPart qIndexMap partMap
--     linearGates = synthDistributed ids finalMat numQPUs
    
--     -- Generate Reset primitives for every dynamically created bell qubit
--     resetGates  = [Reset bell | bell <- generatedBells]
--   in
--     phaseGates ++ linearGates ++ resetGates

distSynth :: [ID] -> F2Mat -> Int -> [Phase] -> Map F2Vec Int -> Map ID Int -> Map Vertex Block -> ([Primitive], Int)
distSynth ids finalMat numQPUs phases parityToPart qIndexMap partMap =
  let
    (phaseGates, phaseBells) = synthPhases ids numQPUs phases parityToPart qIndexMap partMap
    rawLinearGates = synthDistributed ids finalMat numQPUs
    
    -- Map native qubit IDs to their assigned partition
    env = Map.fromList [ (q, Map.findWithDefault 0 (Wire wIdx) partMap) | (q, wIdx) <- Map.toList qIndexMap ]
    
    -- Ensure fresh Bell IDs by offsetting with the ones used in synthPhases
    startBellIdx = length phaseBells `div` 2
    (routedLinearGates, linearBells) = routeLinearGates rawLinearGates startBellIdx env
    
    resetGates  = [Reset bell | bell <- phaseBells ++ linearBells]
    
    -- Every ebit requires two proxy qubits, so we divide the total generated Bell IDs by 2
    chunkEbits = (length phaseBells + length linearBells) `div` 2
  in
    (phaseGates ++ routedLinearGates ++ resetGates, chunkEbits)

-- extractPhasesAndMatrix :: [ID] -> [Primitive] -> ([Phase], F2Mat)
-- extractPhasesAndMatrix ids circ =
--   let 
--       n = length ids
      
--       -- 1. Initialize the state
--       -- Each qubit starts as a standard basis vector (e.g., 1000, 0100) using 'bitI'
--       initVals = Map.fromList [ (v, (bitI n i, False)) | (v, i) <- zip ids [0..] ]
--       initState = SOP {
--           dim   = n,
--           ivals = initVals,
--           qvals = initVals,
--           terms = Map.empty,
--           phase = 0
--       }

--       -- 2. Run the circuit through TPar's analysis engine
--       -- 'applyGate' simulates the circuit. We only care about the final 'st'.
--       (_, finalSt) = runState (foldM applyGate [] circ) initState

--       -- 3. Extract the Phases
--       -- 'terms' is a Map F2Vec Angle. Map.toList directly converts it to [(F2Vec, Angle)] (which is [Phase])!
--       phases = Map.toList (terms finalSt)

--       -- 4. Extract the Final Matrix B
--       -- 'qvals' maps ID -> (F2Vec, Bool). We extract just the F2Vec for each ID in the correct order.
--       finalVecs = [ fst (qvals finalSt Map.! v) | v <- ids ]
--       finalMat  = fromList finalVecs

--   in (phases, finalMat)

extractPhasesAndMatrix :: [ID] -> [Primitive] -> F2Mat -> ([Phase], F2Mat)
extractPhasesAndMatrix ids circ inMat =
  let 
      n = length ids
      
      -- 1. Initialize the state using the threaded matrix
      initVals = Map.fromList [ (v, (row inMat i, False)) | (v, i) <- zip ids [0..] ]
      initState = SOP {
          dim   = n,
          ivals = initVals,
          qvals = initVals,
          terms = Map.empty,
          phase = 0
      }

      -- 2. Run the circuit through TPar's analysis engine
      (_, finalSt) = runState (foldM applyGate [] circ) initState

      -- 3. Extract the Phases
      phases = Map.toList (terms finalSt)

      -- 4. Extract the Final Matrix B
      finalVecs = [ fst (qvals finalSt Map.! v) | v <- ids ]
      finalMat  = fromList finalVecs

  in (phases, finalMat)

-- Toumas's approach buildDistributedCircuit
buildDistributedCircuit :: Int -> [Primitive] -> IO [Primitive]
buildDistributedCircuit numParts circ = do
  (hyp, qIndexMap, _) <- HG.getNumCuts numParts circ
  
  let numQubits = Map.size qIndexMap
      partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
  partMap <- readPartitionFile partitionPath numQubits
  let getPart wIdx = Map.findWithDefault 0 (Wire wIdx) partMap
      
      idPartitions = [ (qid, getPart wIdx) | (qid, wIdx) <- Map.toList qIndexMap ]
      ids0 = [ qid | (qid, part) <- idPartitions, part == 0 ]
      ids1 = [ qid | (qid, part) <- idPartitions, part == 1 ]
      
      sortedIds = ids0 ++ ids1
      numQpu0   = length ids0
      
      -- 1. Extract KaHyPar parities sequentially in the original qubit order
      origQubits = map fst $ sortBy (comparing snd) $ Map.toList qIndexMap
      origParities = HG.extractParities origQubits circ
      n = length origQubits
      
      -- 2. Translate F2Vec from origQubits basis to sortedIds basis
      translateParity p = 
        let activeQs = [ origQubits !! k | k <- [0..n-1], p @. k ]
            bools = [ (sortedIds !! i) `elem` activeQs | i <- [0..n-1] ]
        in fromBits (reverse bools)
        
      translatedParities = map translateParity origParities
      
      -- 3. Lock translated parities to KaHyPar's GateIdx assignments 
      parityToPart = Map.fromList [ (tp, Map.findWithDefault 0 (GateIdx (n + 1 + j)) partMap) 
                                  | (tp, j) <- zip translatedParities [0..] ]
  
  -- 4. Chunk circuit: Group into Phase Polynomial (PP) blocks and Non-PP blocks
  let isPP (CNOT _ _) = True
      isPP g | isZBasisPhaseGate g = True
      isPP _ = False

      chunks = groupBy (\g1 g2 -> isPP g1 == isPP g2) circ

  -- 5. Synthesize chunks, threading the boolean matrix state
  let initialMat = identity n
      initialEbits = 0

      processChunk :: ([Primitive], F2Mat, Int) -> [Primitive] -> ([Primitive], F2Mat, Int)
      processChunk (accCirc, currentMat, accEbits) chunk
        | null chunk = (accCirc, currentMat, accEbits)
        | not (isPP (head chunk)) = 
            -- Non-PP block (e.g., Hadamards): Reset tracking matrix to Identity
            (accCirc ++ chunk, identity n, accEbits)
        | otherwise =
            let (phases, finalMat) = extractPhasesAndMatrix sortedIds chunk currentMat
                -- Unpack the synthesized chunk and its local ebit cost
                (synths, chunkEbits) = distSynth sortedIds finalMat numQpu0 phases parityToPart qIndexMap partMap
            in (accCirc ++ synths, finalMat, accEbits + chunkEbits)

  -- Fold over chunks to thread the state and accumulate the ebit cost
  let (distributedCirc, _, totalEbits) = foldl' processChunk ([], initialMat, initialEbits) chunks
  let partitions = Map.fromList idPartitions

  putStrLn   "# Qubit partition assignments:"
  putStrLn $ "#   QPU 0 (" ++ show (length ids0) ++ " qubits): " ++ unwords (sortBy compare ids0)
  putStrLn $ "#   QPU 1 (" ++ show (length ids1) ++ " qubits): " ++ unwords (sortBy compare ids1)
  
  -- Print the total cost to the console
  putStrLn $ "# Total ebit cost (Synthesis): " ++ show totalEbits
  
  if verifyDist distributedCirc partitions
    then putStrLn "# Distribution Verification: PASS"
    else putStrLn "# Distribution Verification: FAIL (cross-partition gate detected)"
  
  return distributedCirc