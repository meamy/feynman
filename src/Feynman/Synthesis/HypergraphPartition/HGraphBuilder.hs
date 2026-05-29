module Feynman.Synthesis.HypergraphPartition.HGraphBuilder where
import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg

-- Data library
import qualified Data.Map as Map
import           Data.Map   (Map)
import Data.List (isPrefixOf, isInfixOf, maximumBy, sort, sortBy, nub, intercalate)
import Data.Char (isDigit)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Ord (comparing)

-- System library
import System.Directory (doesFileExist, renameFile, removeFile, listDirectory, createDirectoryIfMissing ,getModificationTime)
import System.Exit (ExitCode(..))
import System.FilePath  ((</>), (<.>))
import System.Process (readProcessWithExitCode, callProcess)
import System.IO (hPutStrLn, stderr)

import Control.Monad (unless,  when)
import Feynman.Core
    ( Circuit(..),
      Primitive(..),
      getArgs,
      foldCirc,
      Decl(..),
      foldStmt,
      Stmt(..),
      ID,
      Hypergraph(..),
      Hyperedge, Vertex(..), isCZ, isCNOT,isZBasisPhaseGate ,ids, Block)

import Feynman.Algebra.Linear (F2Vec, bitI, (@.))

-- -- Define WireRole for hyperedge weights
-- data WireRole = Control | Target deriving (Eq, Show)

-- vertexNum :: Vertex -> Int
-- vertexNum (Wire i) = i
-- vertexNum (GateIdx i) = i

-- packCircuit :: [Primitive] -> Circuit
-- packCircuit circ = Circuit { qubits = ids circ,
--                              inputs = Set.fromList (ids circ),
--                              decls  = [main] }
--     where main = Decl { name = "main",
--                         params = [],
--                         body = Seq $ map Gate circ
--                       }

-- -- Build the hypergraph with Physics-Aware early-breaking logic
-- buildHypergraph :: Circuit -> (Int, Hypergraph, Map ID Int)
-- buildHypergraph circuit =
--   let qs           = qubits circuit
--       nQubits      = length qs
--       startCNOT    = nQubits + 1
--       qIndexMap    = Map.fromList (zip qs [1..])

--       stmts = [ g | Decl _ _ (Seq st) <- decls circuit, Gate g <- st ]
      
--       cnotPositions = [ idx | (g, idx) <- zip stmts [0..], isCNOT g ]
--       cnotMap       = Map.fromList $ zip cnotPositions [startCNOT..]

--       symDiff s x = if Set.member x s then Set.delete x s else Set.insert x s

--       weightOf Control = 1
--       weightOf Target  = 2

--       -- fold state: (Active Tabs, Current Edges, Finished Edges)
--       folder (tabs, curr, finished) (pos, gate) =
--         let
--           -- 1. Check if a delayed phase correction tab must be flushed
--           mustFlush (tgt, ctrls) = not (Set.null ctrls) && case gate of
--               CNOT _ t -> Set.member t ctrls                     
--               _        -> any (`Set.member` ctrls) (getArgs gate) 
          
--           flushedTargets = [ tgt | (tgt, ctrls) <- Map.toList tabs, mustFlush (tgt, ctrls) ]

--           -- 2. Also flush if a wire's role changes, OR if a non-CNOT touches an active wire
--           directTouches = case gate of
--               CNOT ctrl tgt -> 
--                   let ctrlChange = case Map.lookup ctrl curr of
--                                      Just (_, Target) -> [ctrl]
--                                      _ -> []
--                       tgtChange  = case Map.lookup tgt curr of
--                                      Just (_, Control) -> [tgt]
--                                      _ -> []
--                   in ctrlChange ++ tgtChange
--               _ -> [ q | q <- getArgs gate, Map.member q curr ]

--           -- Combine all wires that must be severed right now
--           allToFlush = Set.toList $ Set.fromList (flushedTargets ++ directTouches)

--           -- 3. Flush the required wires to the 'finished' list
--           (tabs', curr', finished') = foldl flush (tabs, curr, finished) allToFlush
          
--           flush (tbs, cr, fin) q =
--             case Map.lookup q cr of
--               Nothing -> (tbs, cr, fin)
--               Just (gates, role) ->
--                 let hedge = Set.insert (Wire (qIndexMap Map.! q)) gates
--                     fin'  = if Set.size gates > 0 then (hedge, weightOf role) : fin else fin
--                 in (Map.delete q tbs, Map.delete q cr, fin')

--           -- 4. Update the active tabs and edges for CNOT gates
--           (tabs'', curr'') = case gate of
--             CNOT ctrl tgt ->
--               let idx = cnotMap Map.! pos
--                   gVertex = GateIdx idx
                  
--                   -- Track the error tab for the target
--                   tbs2 = Map.alter (\mbs -> Just (symDiff (case mbs of Just s -> s; Nothing -> Set.empty) ctrl)) tgt tabs'
                  
--                   -- Add this CNOT gate to both the control's edge and the target's edge
--                   cr1 = Map.alter (\mVal -> case mVal of
--                                      Just (gates, r) -> Just (Set.insert gVertex gates, r)
--                                      Nothing         -> Just (Set.singleton gVertex, Control)) ctrl curr'
--                   cr2 = Map.alter (\mVal -> case mVal of
--                                      Just (gates, r) -> Just (Set.insert gVertex gates, r)
--                                      Nothing         -> Just (Set.singleton gVertex, Target)) tgt cr1
--               in (tbs2, cr2)
--             _ -> (tabs', curr')

--         in (tabs'', curr'', finished')

--       -- Execute the fold over the circuit
--       (finalTabs, finalCurr, finalFinished) = foldl folder (Map.empty, Map.empty, []) (zip [0..] stmts)

--       -- Flush any remaining edges at the very end of the circuit
--       flushAll fin q mVal = case mVal of
--         (gates, role) -> 
--            let hedge = Set.insert (Wire (qIndexMap Map.! q)) gates
--            in if Set.size gates > 0 then (hedge, weightOf role) : fin else fin
           
--       allEdges = Map.foldlWithKey flushAll finalFinished finalCurr
      
--       vs = Set.unions (map fst allEdges)
--   in (nQubits, Hypergraph vs allEdges, qIndexMap)

-- hypToString :: Int -> Hypergraph -> String
-- hypToString nQubits (Hypergraph vs hs) =
--   let numH      = length hs
--       numV      = Set.size vs
--       header    = unwords [show numH, show numV, "11"]
      
--       -- Sort edges primarily by Wire ID, secondarily by their first GateIdx
--       edgeSortKey (hedge, _) =
--         let vList = Set.toList hedge
--             wires = [i | Wire i <- vList]
--             gates = [i | GateIdx i <- vList]
--         in (listToMaybe wires, listToMaybe (sort gates))
        
--       sortedHs = sortBy (comparing edgeSortKey) hs

--       edgeLines =
--         [ unwords (show w : map show (sort . map vertexNum . Set.toList $ hedge))
--         | (hedge, w) <- sortedHs 
--         ]
--       weights     = [1 | _ <- [1..nQubits]] ++ [0 | _ <- [nQubits+1..numV]]
--       weightLines = map show weights
--   in unlines $ header : edgeLines ++ weightLines

-- -- | Write a hypergraph to a .hgr file under the "hypergraph" directory (created if missing).
-- --   The file will be named <name>.hgr.
-- writeHypToFile :: String -> Int -> Hypergraph -> IO FilePath
-- writeHypToFile name nQubits hyp = do
--   let dir      = Cfg.hypergraphPartitionDataPath
--       filePath = dir </> name <.> "hgr"
--       contents = hypToString nQubits hyp
--   createDirectoryIfMissing True dir
--   writeFile filePath contents
--   return filePath

-- -- | Build and partition, invoking KaHyPar with correct flags
-- getNumCuts :: Int -> [Primitive] -> IO (Hypergraph, Map ID Block, [Primitive])
-- getNumCuts numParts circ = do
--   let tempDir      = Cfg.hypergraphPartitionDataPath
--       hypergraphFN = "hypergraph.hgr"
--       partitionFN  = "partition.hgr"
--       hypergraphFP = tempDir </> hypergraphFN
--       partitionFP  = tempDir </> partitionFN
--       kahypar      = Cfg.kahyparPath

--   -- Build and write hypergraph
--   let (nQubits, hyp, qIndexMap) = buildHypergraph $ packCircuit circ

--    -- Clamp the number of partitions to the number of qubits
--   let k = min (fromIntegral numParts) (max 1 nQubits)
--   filePath <- writeHypToFile "hypergraph" nQubits hyp
--   when (filePath /= hypergraphFP) $ do
--     existsInitial <- doesFileExist filePath
--     unless existsInitial $
--       error $ "Expected hypergraph file not found at: " ++ filePath
--     renameFile filePath hypergraphFP

--   -- Ensure .hgr exists
--   exists <- doesFileExist hypergraphFP
--   unless exists $
--     error $ "Hypergraph file not found: " ++ hypergraphFP

--   -- Ensure KaHyPar binary exists
--   execExists <- doesFileExist kahypar
--   unless execExists $
--     error $ "Cannot find KaHyPar executable at: " ++ kahypar

--   let args =
--         [ "-h", hypergraphFP
--         , "-k", show k
--         , "-e", show Cfg.epsilon
--         , "-o", "km1"
--         , "-m", "direct"
--         , "-p", Cfg.subalgorithm
--         , "-w", "true"
--         ]
--   (ec, out, err) <- readProcessWithExitCode kahypar args ""
--   let allOut = out ++ err
--   case ec of
--     ExitSuccess -> pure ()
--     _ -> do
--       hPutStrLn stderr $ "KaHyPar failed.\n--- stdout ---\n" ++ out ++ "\n--- stderr ---\n" ++ err
--       error "KaHyPar exited with an error."

--   -- Find latest partition file and rename ===
--   candFiles <- listDirectory tempDir
--   let isPart f = ("hypergraph.hgr.part" `isPrefixOf` f) || (".KaHyPar" `isInfixOf` f)
--       parts    = [ f | f <- candFiles, isPart f ]
--   when (null parts) $
--     error "KaHyPar did not produce a partition file."
--   times <- mapM (\f -> getModificationTime (tempDir </> f) >>= \t -> pure (f,t)) parts
--   let latest = fst $ maximumBy (comparing snd) times
--   existing <- doesFileExist partitionFP
--   when existing $ removeFile partitionFP
--   renameFile (tempDir </> latest) partitionFP

--   case parseHyperedgeCut allOut of
--     Just cut -> putStrLn $ "# Hyperedge cut (ebits): " ++ show cut ++ "\n"
--     Nothing  -> hPutStrLn stderr "Warning: could not parse Hyperedge Cut from KaHyPar output."

--   return (hyp, qIndexMap, circ)

ordNub :: Ord a => [a] -> [a]
ordNub = go Set.empty
  where
    go _ [] = []
    go seen (x:xs)
      | Set.member x seen = go seen xs
      | otherwise         = x : go (Set.insert x seen) xs

extractParities :: [ID] -> [Primitive] -> [F2Vec]
-- extractParities qubits circ = reverse . nub $ go initSt circ []
extractParities qubits circ = ordNub . reverse $ go initSt circ []
  where
    initSt = Map.fromList [(q, bitI (length qubits) i) | (q,i) <- zip qubits [0..]]

    go st [] acc = acc
    go st (g:gs) acc = case g of
      CNOT c t ->
        let cVal = Map.findWithDefault 0 c st
            tVal = Map.findWithDefault 0 t st
            st' = Map.insert t (cVal + tVal) st
        in go st' gs acc
      _ | isZBasisPhaseGate g ->
        case getArgs  g of
          (q:_) -> let p = Map.findWithDefault 0 q st in go st gs (p:acc)
          [] -> go st gs acc
      _ -> go st gs acc

buildParityHypergraph :: [ID] -> [F2Vec] -> Hypergraph
buildParityHypergraph qubits parities = Hypergraph allVertices hEdges
  where
    n = length qubits 
    m = length parities

    qubitVertices = [Wire i | i <- [1..n]]
    parityVertices = [GateIdx (n + 1 + j) | j <- [0..m-1]]
    
    allVertices    = Set.fromList (qubitVertices ++ parityVertices)

    hEdges = [ (buildEdgeForQubit i, 1) | i <- [0..n-1] ]
    buildEdgeForQubit :: Int -> Hyperedge
    buildEdgeForQubit i =
      let nativeQubitVertex = Wire (i + 1)
          associatedParities = [ GateIdx (n + 1 + j) 
                               | j <- [0..m-1]
                               , parities !! j @. i ] -- Uses the bit-test operator from Gray.hs
      in Set.fromList (nativeQubitVertex : associatedParities)

hypToString :: Int -> Int -> Hypergraph -> String
hypToString nQubits mParities (Hypergraph vs hs) =
  let numH      = length hs
      numV      = Set.size vs
      header    = unwords [show numH, show numV, "10"]

      edgeLines = [ unwords (map showVertex (Set.toList hedge)) 
                  | (hedge, _) <- hs ]

      weightLines = replicate nQubits "1" ++ replicate mParities "0"
                  
  in unlines $ header : (edgeLines ++ weightLines)
  where
    showVertex (Wire i)    = show i
    showVertex (GateIdx i) = show i


showParity :: [ID] -> F2Vec -> String
showParity qubits vec =
  let activeQubits = [ qubits !! i 
                     | i <- [0 .. length qubits - 1]
                     , vec @. i ] -- Checks if the i-th qubit is active in this parity
  in if null activeQubits 
     then "0" 
     else intercalate " + " activeQubits


getNumCuts :: Int -> [Primitive] -> IO (Hypergraph, Map ID Int, [Primitive])
getNumCuts numParts circ = do
  let tempDir      = Cfg.hypergraphPartitionDataPath
      hypergraphFN = "hypergraph.hgr"
      partitionFN  = "partition.hgr"
      hypergraphFP = tempDir </> hypergraphFN
      partitionFP  = tempDir </> partitionFN
      kahypar      = Cfg.kahyparPath
      
      qubitsList   = ids circ
      nQubits      = length qubitsList
      parities     = extractParities qubitsList circ
      mParities    = length parities
      k            = min (fromIntegral numParts) (max 1 nQubits)

  putStrLn "\n========================================================"
  putStrLn $ "# Extracted Qubits: " ++ show nQubits
  putStrLn $ "# Extracted Phase Polynomial Parities: " ++ show mParities
  putStrLn "========================================================"

  putStrLn "# Explicit List of Extracted Unique Parities:"
  mapM_ (\(idx, p) -> 
    putStrLn $ "  * Vertex " ++ show (nQubits + 1 + idx) ++ " -> " ++ showParity qubitsList p
    ) (zip [0..] parities)
  putStrLn "========================================================"

  -- 1. Build the updated dual-vertex layout
  let parityHyp = buildParityHypergraph qubitsList parities
  let qIndexMap = Map.fromList (zip qubitsList [1..])

  -- 2. Clean/Prepare directory and serialize graph data
  createDirectoryIfMissing True tempDir
  writeFile hypergraphFP (hypToString nQubits mParities parityHyp)

  let args = [ "-h", hypergraphFP, "-k", show k, "-e", show Cfg.epsilon, "-o", "km1", "-m", "direct", "-p", Cfg.subalgorithm, "-w", "true" ]
  (ec, out, err) <- readProcessWithExitCode kahypar args ""
  
  case ec of
    ExitSuccess -> pure ()
    _ -> do
      hPutStrLn stderr $ "KaHyPar failed.\n--- stdout ---\n" ++ out ++ "\n--- stderr ---\n" ++ err
      error "KaHyPar exited with an error."

  -- 4. Locate and bind the generated partition file
  candFiles <- listDirectory tempDir
  let isPart f = ("hypergraph.hgr.part" `isPrefixOf` f) || (".KaHyPar" `isInfixOf` f)
      parts    = [ f | f <- candFiles, isPart f ]
  when (null parts) $ error "KaHyPar did not produce a partition file."
  
  times <- mapM (\f -> getModificationTime (tempDir </> f) >>= \t -> pure (f,t)) parts
  let latest = fst $ maximumBy (comparing snd) times
  existing <- doesFileExist partitionFP
  when existing $ removeFile partitionFP
  renameFile (tempDir </> latest) partitionFP

  case parseHyperedgeCut out of
    Just cut -> putStrLn $ "# Hyperedge cut (ebits metric): " ++ show cut ++ "\n"
    Nothing  -> hPutStrLn stderr "Warning: could not parse Hyperedge Cut from KaHyPar output."

  return (parityHyp, qIndexMap, circ)

parseHyperedgeCut :: String -> Maybe Int
parseHyperedgeCut s =
  let linesWith = filter (isInfixOf "Hyperedge Cut") (lines s)
      grabInt ln =
        let ws = reverse (words ln)
        in listToMaybe [ read w :: Int | w <- ws, all isDigit w ]
  in listToMaybe (mapMaybe grabInt linesWith)