module Feynman.Synthesis.HypergraphPartition.HGraphBuilder where
import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg

import qualified Data.Map as Map
import           Data.Map   (Map)
import           Data.List (isPrefixOf, isInfixOf, maximumBy, sort)
import Data.Char (isDigit)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (listToMaybe)

import Data.Ord (comparing)

import System.Directory (doesFileExist, renameFile, removeFile, listDirectory, createDirectoryIfMissing ,getModificationTime)
import System.Exit (ExitCode(..))
import System.FilePath  ((</>), (<.>))
import System.Process (callProcess)
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode, callProcess)

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
      Hyperedge, Vertex(..), isCZ, isCNOT,ids,getArgs)
import Test.QuickCheck.Test (test)
import Feynman.Algebra.Polynomial.Multilinear (distribute)

packCircuit :: [Primitive] -> Circuit
packCircuit circ = Circuit { qubits = ids circ,
                             inputs = Set.fromList (ids circ),
                             decls  = [main] }
    where main = Decl { name = "main",
                        params = [],
                        body = Seq $ map Gate circ
                      }

-- -- | Build the hypergraph for a given Circuit
-- --   Qubits are numbered 1..n in declaration order, CZ gates are globally numbered starting at n+1.
-- --   Heunen's original approach for CZ gates
-- buildHypergraph :: Circuit -> (Int, Hypergraph)
-- buildHypergraph circuit =
--   let qs           = qubits circuit
--       nQubits      = length qs
--       startCZ      = nQubits + 1
--       qIndexMap    = Map.fromList (zip qs [1..])

--       -- flatten all primitives in declaration order with their positions
--       allPrimsWithIdx :: [(Primitive, Int)]
--       allPrimsWithIdx =
--         [ (p, idx)
--         | Decl _ _ (Seq stmts) <- decls circuit
--         , (Gate p, idx)       <- zip stmts [0..]
--         ]

--       -- assign global CZ indices by original position
--       czPositions = [ pos | (p,pos) <- allPrimsWithIdx, isCZ p ]
--       czMap       = Map.fromList $ zip czPositions [startCZ..]

--       -- extract primitives acting on q, keeping their positions
--       qubitGatesWithIdx q =
--         [ (p,pos)
--         | (p,pos) <- allPrimsWithIdx
--         , q `elem` getArgs p
--         ]

--       -- process each wire into its hyperedges (emitting only after seeing a CZ)
--       buildForWire q =
--         let wireIdx = qIndexMap Map.! q
--             prims   = qubitGatesWithIdx q
--             -- Stateful walk: czSeen tracks if we've started a hedge
--             go :: Bool -> Hyperedge -> [(Primitive,Int)] -> [Hyperedge]
--             -- End of list: emit only if we saw a CZ
--             go czSeen hedge []
--               | czSeen    = [hedge]
--               | otherwise = []
--             go czSeen hedge ((g,pos):ps)
--               -- extend hedge on CZ
--               | isCZ g && wireIdx `elem` map (qIndexMap Map.!) (getArgs g) =
--                   let idx    = czMap Map.! pos
--                       hedge' = if czSeen
--                                then Set.insert (GateIdx idx) hedge
--                                else Set.fromList [Wire wireIdx, GateIdx idx]
--                   in go True hedge' ps
--               -- on non-CZ, flush previous hedge if any, reset
--               | otherwise =
--                   let out = if czSeen then [hedge] else []
--                   in out ++ go False Set.empty ps
--         in go False Set.empty prims

--       -- collect all hyperedges and vertices
--       hs = concatMap buildForWire qs
--       vs = Set.unions hs
--   in (nQubits, Hypergraph vs hs)

data WireRole = Control | Target deriving (Eq, Show)

-- | Build the hypergraph for a given Circuit with CNOT gates
--   Qubits are numbered 1..n in declaration order, CNOT gates are globally numbered starting at n+1.
--   Based on Heunen's hypergraph approach but implement directly for CNOT gates

buildHypergraph :: Circuit -> (Int, Hypergraph)
buildHypergraph circuit =
  let qs           = qubits circuit
      nQubits      = length qs
      startCNOT    = nQubits + 1
      qIndexMap    = Map.fromList (zip qs [1..])

      -- flatten all primitives in declaration order with their positions
      allPrimsWithIdx :: [(Primitive, Int)]
      allPrimsWithIdx =
        [ (p, idx)
        | Decl _ _ (Seq stmts) <- decls circuit
        , (Gate p, idx)       <- zip stmts [0..]
        ]

      -- assign global CNOT indices by original position
      cnotPositions = [ pos | (p, pos) <- allPrimsWithIdx, isCNOT p ]
      cnotMap       = Map.fromList $ zip cnotPositions [startCNOT..]

      -- get the role of a wire in a CNOT gate
      getRole :: Primitive -> ID -> Maybe WireRole
      getRole (CNOT ctrl tgt) q
        | q == ctrl = Just Control
        | q == tgt  = Just Target
        | otherwise = Nothing
      getRole _ _ = Nothing

      -- extract primitives acting on q, keeping their positions
      qubitGatesWithIdx :: ID -> [(Primitive, Int)]
      qubitGatesWithIdx q =
        [ (p, pos)
        | (p, pos) <- allPrimsWithIdx
        , q `elem` getArgs p
        ]

      -- process each wire into its hyperedges
      buildForWire :: ID -> [Hyperedge]
      buildForWire q =
        let wireIdx = qIndexMap Map.! q
            prims   = qubitGatesWithIdx q

            -- Stateful walk: 
            --   cnotSeen: Is a hyperedge creating right now?
            --   currentRole: is qubit control or target in CNOT gate
            go :: Bool -> Maybe WireRole -> Hyperedge -> [(Primitive, Int)] -> [Hyperedge]
            -- End of list: emit only if we saw a CNOT
            go True _ hedge [] = [hedge]
            go False _ _ []    = []

            go cnotSeen currentRole hedge ((g, pos):ps) = case g of
              CNOT ctrl tgt ->
                let idx      = cnotMap Map.! pos
                    thisRole = getRole g q
                in case (cnotSeen, currentRole, thisRole) of
                     -- First CNOT on this wire: start new hyperedge
                     (False, _, Just role) ->
                       let hedge' = Set.fromList [Wire wireIdx, GateIdx idx]
                       in go True (Just role) hedge' ps

                     -- Continuing with same role: extend hyperedge
                     (True, Just r, Just role) | r == role ->
                       let hedge' = Set.insert (GateIdx idx) hedge
                       in go True currentRole hedge' ps

                     -- Role changed: close current, start new
                     (True, Just _, Just role) ->
                       let newHedge = Set.fromList [Wire wireIdx, GateIdx idx]
                       in hedge : go True (Just role) newHedge ps

                     -- Not happen if q is in getArgs
                     _ -> go cnotSeen currentRole hedge ps

              -- Non-CNOT gate: flush current hyperedge if any, reset
              _ -> if cnotSeen
                   then hedge : go False Nothing Set.empty ps
                   else go False Nothing Set.empty ps

        in go False Nothing Set.empty prims

      -- collect all hyperedges and vertices
      hs = concatMap buildForWire qs
      vs = Set.unions hs
  in (nQubits, Hypergraph vs hs)

-- | Extract the numeric ID from a Vertex
vertexNum :: Vertex -> Int
vertexNum (Wire i) = i
vertexNum (GateIdx i) = i

hypToString :: Int -> Hypergraph -> String
hypToString nQubits (Hypergraph vs hs) =
  let numH      = length hs
      numV      = Set.size vs
      header    = unwords [show numH, show numV, "10"]
      edgeLines =
        [ unwords . map show . sort . map vertexNum . Set.toList $ hedge
        | hedge <- hs
        ]
      weights     = [1 | _ <- [1..nQubits]]
                 ++ [0 | _ <- [nQubits+1..numV]]
      weightLines = map show weights
  in unlines $ header : edgeLines ++ weightLines

-- | Write a hypergraph to a .hgr file under the "Temp" directory (created if missing).
--   The file will be named <name>.hgr.
writeHypToFile :: String -> Int -> Hypergraph -> IO FilePath
writeHypToFile name nQubits hyp = do
  let dir      = Cfg.hypergraphPartitionDataPath
      filePath = dir </> name <.> "hgr"
      contents = hypToString nQubits hyp
  createDirectoryIfMissing True dir
  writeFile filePath contents
  return filePath

-- | Build and partition, invoking KaHyPar with correct flags
getNumCuts :: [Primitive] -> IO [Primitive]
getNumCuts circ = do
  let tempDir      = Cfg.hypergraphPartitionDataPath
      hypergraphFN = "hypergraph.hgr"
      partitionFN  = "partion.hgr"
      hypergraphFP = tempDir </> hypergraphFN
      partitionFP  = tempDir </> partitionFN
      k            = Cfg.numParts
      kahypar      = Cfg.kahyparPath
  
  putStrLn $ "# Partition result"

  -- Build and write hypergraph
  let (nQuibits, hyp) = buildHypergraph $ packCircuit circ
  filePath <- writeHypToFile "hypergraph" nQuibits hyp
  when (filePath /= hypergraphFP) $ do
    existsInitial <- doesFileExist filePath
    unless existsInitial $
      error $ "Expected hypergraph file not found at: " ++ filePath
    renameFile filePath hypergraphFP
  putStrLn $ "# Hypergraph written to: " ++ hypergraphFP

  -- Ensure .hgr exists
  exists <- doesFileExist hypergraphFP
  unless exists $
    error $ "Hypergraph file not found: " ++ hypergraphFP

  -- Ensure KaHyPar binary exists
  execExists <- doesFileExist kahypar
  unless execExists $
    error $ "Cannot find KaHyPar executable at: " ++ kahypar

  let args =
        [ "-h", hypergraphFP
        , "-k", show k
        , "-e", Cfg.epsilon
        , "-o", "km1"
        , "-m", "direct"
        , "-p", Cfg.subalgorithm
        , "-w", "true"
        -- ensure not quiet, so it prints metrics (omit -q or pass -q false if your KaHyPar needs it)
        ]
  (ec, out, err) <- readProcessWithExitCode kahypar args ""
  let allOut = out ++ err
  case ec of
    ExitSuccess -> pure ()
    _ -> do
      hPutStrLn stderr $ "KaHyPar failed.\n--- stdout ---\n" ++ out ++ "\n--- stderr ---\n" ++ err
      error "KaHyPar exited with an error."

  -- === continue: find latest partition file and rename ===
  candFiles <- listDirectory tempDir
  let isPart f = ("hypergraph.hgr.part" `isPrefixOf` f) || (".KaHyPar" `isInfixOf` f)
      parts    = [ f | f <- candFiles, isPart f ]
  when (null parts) $
    error "KaHyPar did not produce a partition file."
  times <- mapM (\f -> getModificationTime (tempDir </> f) >>= \t -> pure (f,t)) parts
  let latest = fst $ maximumBy (comparing snd) times
  existing <- doesFileExist partitionFP
  when existing $ removeFile partitionFP
  renameFile (tempDir </> latest) partitionFP
  putStrLn $ "# Partition file written to: " ++ partitionFP

   -- Parse "Hyperedge Cut : <N>"
  case parseHyperedgeCut allOut of
    Just cut -> putStrLn $ "# Hyperedge cut (ebits): " ++ show cut ++ "\n"
    Nothing  -> hPutStrLn stderr "Warning: could not parse Hyperedge Cut from KaHyPar output."

  return circ

-- Note for pseudocode of distribute function

-- pointsTo :: [AccessPath] -> SExpr -> Assertion

-- distribute :: KaHyperData -> [Primitive] -> [Primitive]
-- distribute data circuit = go 0 circuit
--   where 
--     go i [] = []
--     go i (gates) = 
--       if gate is local
--       else if no wire allocated
--         (b1, b2) = initialize bell pair i
--         i = i+2
--         CNOT gateCtrl b1
  


parseHyperedgeCut :: String -> Maybe Int
parseHyperedgeCut s =
  let linesWith = filter (isInfixOf "Hyperedge Cut") (lines s)
      grabInt ln =
        let ws = reverse (words ln)
        in listToMaybe [ read w :: Int | w <- ws, all isDigit w ]
  in listToMaybe (mapMaybe grabInt linesWith)

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f = foldr (\x acc -> case f x of Just y -> y:acc; _ -> acc) []
