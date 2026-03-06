-- module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where

-- import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
-- import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
-- import Feynman.Core (Primitive(..), getArgs, ID, isCNOT, PartitionData, Block)
-- import qualified Data.Map as Map
-- import Data.Map (Map)
-- import System.FilePath ((</>))

-- bellState :: ID -> ID -> [Primitive]
-- bellState bell1 bell2 = [H bell1, CNOT bell1 bell2]

-- catEntangler :: ID -> ID -> ID -> [Primitive]
-- catEntangler srcQubit bell1 bell2 = bellState bell1 bell2 ++
--     [   CNOT srcQubit bell2,
--         Measure bell2,
--         CNOT bell2 bell1
--     ]

-- catDisentangler :: ID -> ID -> Primitive
-- catDisentangler srcQubit bell = CZ bell srcQubit 

-- readPartitionFile :: FilePath -> Map ID Block -> IO PartitionData
-- readPartitionFile filepath idToWireMap = do
--   contents <- readFile filepath
--   let partLines = lines contents
--       numQubits = Map.size idToWireMap
      
--       -- Build reverse mapping: Wire → ID
--       -- idToWireMap is ID → Wire, we need Wire → ID
--       wireToID = Map.fromList [(wire, qid) | (qid, wire) <- Map.toList idToWireMap]
      
--       -- Read partition assignments for qubits only
--       -- (First numQubits lines are qubits, rest are gates)
--       -- Convert Wire indices to IDs
--       partitionAssignments = 
--         [   (wireToID Map.! wire, read part :: Int)
--           | (wire, part) <- zip [1..numQubits] (take numQubits partLines)
--         ]
  
--   return $ Map.fromList partitionAssignments

  
-- nonLocals :: [Primitive] -> PartitionData -> IO ()
-- nonLocals circ partition = mapM_ checkGate (filter isCNOT circ)
--   where
--     checkGate gate = 
--         let args = getArgs gate
--             partitions = mapM (`Map.lookup` partition) args
--         in case partitions of
--                Just (b:bs) | all (== b) bs -> 
--                  putStrLn $ show gate ++ " is local (partition " ++ show b ++ ")"
--                Just [b1, b2] -> 
--                  putStrLn $ show gate ++ " is non-local (partitions " 
--                             ++ show b1 ++ " != " ++ show b2 ++ ")"
--                _ -> 
--                  putStrLn $ show gate ++ " - partition lookup failed"


-- buildDistributedCircuit :: [Primitive] -> IO [Primitive]
-- buildDistributedCircuit circ = do
--   (_, idToWireMap, _) <- HG.getNumCuts circ
--   let partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
--   partition <- readPartitionFile partitionPath idToWireMap

--   -- nonLocals circ partition 
  
--   return circ

module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import Feynman.Core (Primitive(..), getArgs, ID, isCZ, Block, Vertex(..), Hypergraph(..), Hyperedge, substGate)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import System.FilePath ((</>))

catEntangler :: ID -> ID -> ID -> [Primitive]
catEntangler srcQubit bell1 bell2 = 
    [   H bell1,
        CNOT bell1 bell2,
        CNOT srcQubit bell2,
        Measure bell2,
        CNOT bell2 bell1
    ]

catDisentangler :: ID -> ID -> [Primitive]
catDisentangler srcQubit bell = 
    [   H bell,
        Measure bell,
        CZ bell srcQubit
    ]

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
getTeleportationBoundaries (Hypergraph _ hedges) partMap = mapMaybe analyzeEdge hedges
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
synthesizeDistributed :: [Primitive] -> Int -> Map ID Int -> Map Vertex Block -> [(Vertex, Int, Int)] -> [Primitive]
synthesizeDistributed circ numQubits qIndexMap partMap boundaries =
  let -- Reverse map to look up ID string from Wire index
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

buildDistributedCircuit :: [Primitive] -> IO [Primitive]
buildDistributedCircuit circ = do
  -- Extract hypergraph, index map, and circuit
  (hyp, qIndexMap, _) <- HG.getNumCuts circ
  
  let numQubits = Map.size qIndexMap
      partitionPath = Cfg.hypergraphPartitionDataPath </> "partition.hgr"
      
  partMap <- readPartitionFile partitionPath numQubits
  let boundaries = getTeleportationBoundaries hyp partMap
  
  let distributedCirc = synthesizeDistributed circ numQubits qIndexMap partMap boundaries
  
  return distributedCirc