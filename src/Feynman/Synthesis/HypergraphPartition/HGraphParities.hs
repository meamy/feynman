module Feynman.Synthesis.HypergraphPartition.HGraphParities
  ( ParityHG(..)
  , ParityOpts(..)
  , BreakScope(..)
  , defaultParityOpts
  , buildParityHG
  , buildParityHGFromPrims
  , buildParityHGOver
  , buildParityHGWith
  , phgKm1
  , phgCutNet
  , parityHGToHypergraph
  , parityHGToHMetis
  , showParityHG
  , partitionParityHG
  , partitionParityHGWith
  , parityHGAssignment
  , readParityHGPartition
  ) where

import qualified Data.Map as Map
import           Data.Map   (Map)
import qualified Data.Set as Set
import           Data.Set   (Set)
import           Data.List  (foldl', intercalate, isPrefixOf)
import           Control.Exception (evaluate)
import           Control.Monad (forM_)
import           System.Directory (createDirectoryIfMissing, listDirectory, removeFile)
import           System.Exit (ExitCode(..))
import           System.FilePath ((</>))
import           System.IO (hPutStrLn, stderr)
import           System.Process (readProcessWithExitCode)

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import           Feynman.Synthesis.HypergraphPartition.QIGBuilder (parsePartition)

import Feynman.Core
    ( Circuit(..), Decl(..), Stmt(..), Primitive(..), ID
    , getArgs, ids, isZBasisPhaseGate, Hypergraph(..), Vertex(..) )

{-----------------------------------
 Types
 -----------------------------------}

data ParityHG = ParityHG
  { phgNumQubits :: Int
  , phgIndex     :: Map ID Int         -- qubit name -> vertex (1-based)
  , phgEdges     :: Map (Set Int) Int  -- qubit set (>= 2 vertices) -> number of runs
  } deriving (Show)

-- | Which wires lose their parity when a run-stopping gate is met.
data BreakScope
  = BreakWire  -- ^ only the wires the gate acts on. Parities that live on
               --   other wires keep running.
  | BreakAll   -- ^ every wire, like the global reset in
               --   'HGraphBuilder.extractParities'. Every parity seen after
               --   the gate is a new run, but parities built up before it on
               --   untouched wires are forgotten.
  deriving (Eq, Show)

data ParityOpts = ParityOpts
  { optBreakScope     :: BreakScope
  , optOutputParities :: Bool
    -- ^ Also add a hyperedge for the parity a wire carries when its run is
    --   stopped and at the end of the circuit (the linear part of the
    --   circuit), not only for parities that receive a phase gate. Such a
    --   hyperedge contains the wire itself as well. With this off, CNOTs
    --   whose result never meets a phase gate leave no trace: e.g.
    --   @CNOT a b; H b@ gives no hyperedge.
  } deriving (Eq, Show)

-- | Per-wire breaks, phase-gate parities only.
defaultParityOpts :: ParityOpts
defaultParityOpts = ParityOpts { optBreakScope = BreakWire, optOutputParities = False }

-- | Build the parity hypergraph from a Circuit. Nested 'Seq' blocks are
--   flattened and 'Repeat k' is unrolled k times. 'Call' statements are not
--   inlined, so inline subroutines first if your circuits use them.
buildParityHG :: Circuit -> ParityHG
buildParityHG circuit =
  buildParityHGWith defaultParityOpts (qubits circuit) (concatMap (flatten . body) (decls circuit))
  where
    flatten :: Stmt -> [Primitive]
    flatten (Gate g)     = [g]
    flatten (Seq st)     = concatMap flatten st
    flatten (Repeat i s) = concat (replicate i (flatten s))
    flatten (Call _ _)   = []

-- | Build from a flat gate list, as 'getNumCuts' receives it. Uses
--   'ids circ' for numbering, matching the qIndexMap in 'getNumCuts'.
buildParityHGFromPrims :: [Primitive] -> ParityHG
buildParityHGFromPrims circ = buildParityHGWith defaultParityOpts (ids circ) circ

-- | Build over an explicit qubit list, so declared-but-idle qubits still get
--   a vertex (same numbering as 'buildQIGOver' for the same arguments).
buildParityHGOver :: [ID] -> [Primitive] -> ParityHG
buildParityHGOver = buildParityHGWith defaultParityOpts

-- | General builder. Qubits used by the circuit but missing from the list
--   are appended, so every qubit the circuit touches is always a vertex.
buildParityHGWith :: ParityOpts -> [ID] -> [Primitive] -> ParityHG
buildParityHGWith opts qs circ = ParityHG (length allQs) qIndex (stEdges final)
  where
    declared = Set.fromList qs
    allQs    = qs ++ [ q | q <- ids circ, not (Set.member q declared) ]
    qIndex   = Map.fromList (zip allQs [1..])

    -- Qubit i starts with path variable i, owned by vertex i.
    start = St { stWire  = Map.map Set.singleton qIndex
               , stOwner = Map.fromList [ (i, i) | i <- Map.elems qIndex ]
               , stNext  = length allQs + 1
               , stSeen  = Set.empty
               , stEdges = Map.empty }

    walked = foldl' (step opts qIndex) start circ
    final
      | optOutputParities opts = foldl' (closeWire qIndex) walked allQs
      | otherwise              = walked

-- | A parity: the set of path variables it is the XOR of.
type Parity = Set Int

data St = St
  { stWire  :: !(Map ID Parity)             -- parity currently on each wire
  , stOwner :: !(Map Int Int)               -- path variable -> qubit vertex
  , stNext  :: !Int                         -- next fresh path variable
  , stSeen  :: !(Set (Parity, Maybe Int))   -- runs that already have a hyperedge
  , stEdges :: !(Map (Set Int) Int)
  }

xorP :: Parity -> Parity -> Parity
xorP a b = Set.union (Set.difference a b) (Set.difference b a)

-- | Process one gate. This is the single place that decides which gates
--   continue a run, mark a parity, or stop a run.
step :: ParityOpts -> Map ID Int -> St -> Primitive -> St
step opts qIndex st g = case g of
  CNOT c t
    | c == t    -> st   -- not a valid gate; ignore instead of wiping the wire's parity
    | otherwise -> st { stWire = Map.insert t (xorP (on c) (on t)) (stWire st) }
  Swap a b -> st { stWire = Map.insert a (on b) (Map.insert b (on a) (stWire st)) }
  CZ a b
    | a == b    -> st
    | otherwise -> foldl' (flip (mark Nothing)) st [on a, on b, xorP (on a) (on b)]
  X _      -> st
  Y q      -> mark Nothing (on q) st
  _ | isZBasisPhaseGate g -> foldl' (flip (mark Nothing)) st (map on (getArgs g))
    | otherwise           ->
        let args = getArgs g
            pins = Set.fromList (map (qIndex Map.!) args)
            st'  | Set.size pins >= 2 = st { stEdges = Map.insertWith (+) pins 1 (stEdges st) }
                 | otherwise          = st
        in breakWires opts qIndex (Set.toList (Set.fromList args)) st'
  where
    on q = stWire st Map.! q

-- | Record that parity @p@ is used. The first use of a parity opens its run
--   and adds its qubit set as a hyperedge; later uses of the same parity
--   (same path variables) are part of that run and add nothing.
--   @host@ is an extra pin: the wire carrying the parity, used for output
--   parities only.
mark :: Maybe Int -> Parity -> St -> St
mark host p st
  | Set.member key (stSeen st) = st
  | Set.size pins < 2          = st
  | otherwise                  = st { stSeen  = Set.insert key (stSeen st)
                                    , stEdges = Map.insertWith (+) pins 1 (stEdges st) }
  where
    support = Set.map (stOwner st Map.!) p
    host'   = case host of
                Just w | not (Set.member w support) -> Just w
                _                                   -> Nothing
    pins    = maybe support (`Set.insert` support) host'
    key     = (p, host')

-- | Output parity of a wire: what it carries when its run ends.
closeWire :: Map ID Int -> St -> ID -> St
closeWire qIndex st q = mark (Just (qIndex Map.! q)) (stWire st Map.! q) st

-- | Stop the runs through the given wires by giving them fresh variables.
breakWires :: ParityOpts -> Map ID Int -> [ID] -> St -> St
breakWires opts qIndex qs st0 = foldl' fresh closed targets
  where
    closed
      | optOutputParities opts = foldl' (closeWire qIndex) st0 qs
      | otherwise              = st0
    targets = case optBreakScope opts of
      BreakWire -> qs
      BreakAll  -> Map.keys (stWire st0)
    fresh st q =
      let v = stNext st
      in st { stWire  = Map.insert q (Set.singleton v) (stWire st)
            , stOwner = Map.insert v (qIndex Map.! q) (stOwner st)
            , stNext  = v + 1 }

-- | Number of blocks each hyperedge touches under an assignment, with its
--   weight. Qubits missing from the assignment count as block 0.
edgeSpans :: ParityHG -> Map ID Int -> [(Int, Int)]
edgeSpans hg assignment =
  [ (w, Set.size (Set.map blockOf pins)) | (pins, w) <- Map.toList (phgEdges hg) ]
  where
    byIdx     = Map.fromList [ (i, Map.findWithDefault 0 q assignment)
                             | (q, i) <- Map.toList (phgIndex hg) ]
    blockOf i = Map.findWithDefault 0 i byIdx

-- | Connectivity (km1) metric, the objective KaHyPar is run with:
--   sum over hyperedges of weight * (blocks touched - 1).
phgKm1 :: ParityHG -> Map ID Int -> Int
phgKm1 hg assignment = sum [ w * (lambda - 1) | (w, lambda) <- edgeSpans hg assignment ]

-- | Cut-net metric: total weight of hyperedges that touch more than one
--   block, i.e. the number of parity runs that are not local to one QPU.
phgCutNet :: ParityHG -> Map ID Int -> Int
phgCutNet hg assignment = sum [ w | (w, lambda) <- edgeSpans hg assignment, lambda > 1 ]

-- | View as the existing Hypergraph type. Idle qubits are kept as vertices.
parityHGToHypergraph :: ParityHG -> Hypergraph
parityHGToHypergraph (ParityHG n _ es) = Hypergraph vs hes
  where
    vs  = Set.fromList [ Wire i | i <- [1..n] ]
    hes = [ (Set.map Wire pins, w) | (pins, w) <- Map.toList es ]

-- | Serialize for KaHyPar in hMetis format with EDGE weights (fmt = 1):
--   each hyperedge line is its weight followed by its vertices. Every
--   vertex is a qubit with (implicit) weight 1, so blocks are balanced by
--   qubit count.
parityHGToHMetis :: ParityHG -> String
parityHGToHMetis (ParityHG n _ es) = unlines (header : edgeLines)
  where
    header    = unwords [show (Map.size es), show n, "1"]
    edgeLines = [ unwords (show w : map show (Set.toAscList pins))
                | (pins, w) <- Map.toList es ]

-- | Human-readable listing, one hyperedge per line: weight, then the parity
--   written over qubit names, e.g. @2  x + y + z@.
showParityHG :: ParityHG -> String
showParityHG hg = unlines
  [ show w ++ "  " ++ intercalate " + " [ nameOf i | i <- Set.toAscList pins ]
  | (pins, w) <- Map.toList (phgEdges hg) ]
  where
    byIdx    = Map.fromList [ (i, q) | (q, i) <- Map.toList (phgIndex hg) ]
    nameOf i = Map.findWithDefault ("#" ++ show i) i byIdx

-- | Build the parity hypergraph over the given qubits, partition it into
--   @numParts@ blocks with KaHyPar, and return it together with the
--   assignment qubit -> block (0 .. k-1). Every qubit in @qs@ and every
--   qubit the circuit touches gets a block, idle ones included.
--
--   Same KaHyPar settings as 'getNumCuts' and 'partitionQIG', but its own
--   file names (parity.hgr / parity.partition), so their files are left
--   alone.
partitionParityHG :: Int -> [ID] -> [Primitive] -> IO (ParityHG, Map ID Int)
partitionParityHG = partitionParityHGWith defaultParityOpts

partitionParityHGWith :: ParityOpts -> Int -> [ID] -> [Primitive] -> IO (ParityHG, Map ID Int)
partitionParityHGWith opts numParts qs circ = do
  let hg = buildParityHGWith opts qs circ
      n  = phgNumQubits hg
      k  = min numParts (max 1 n)

  if k <= 1 || Map.null (phgEdges hg)
    then do
      -- Nothing to cut (one block, or no multi-qubit parity): KaHyPar has no
      -- work to do and may reject an edgeless graph, so split evenly instead.
      let blocks = [ ((i - 1) * k) `div` max 1 n | i <- [1 .. n] ]
      return (hg, parityHGAssignment hg blocks)
    else do
      blocks <- runKaHyPar k n (parityHGToHMetis hg)
      return (hg, parityHGAssignment hg blocks)

-- | Turn one block per vertex (vertex 1 first, as KaHyPar lists them) into
--   the assignment qubit -> block. Expects exactly one block per vertex.
parityHGAssignment :: ParityHG -> [Int] -> Map ID Int
parityHGAssignment hg blocks = Map.map (byVertex Map.!) (phgIndex hg)
  where
    byVertex = Map.fromList (zip [1 ..] blocks)

-- | Read a KaHyPar partition file written for this hypergraph, e.g. the
--   @parity.partition@ copy that 'partitionParityHG' leaves behind.
--   KaHyPar identifies vertices only by line number, so the file must come
--   from a hypergraph built over the same qubit list in the same order.
readParityHGPartition :: ParityHG -> Int -> FilePath -> IO (Map ID Int)
readParityHGPartition hg k fp = do
  blocks <- readPartitionFile ("readParityHGPartition: " ++ fp) k (phgNumQubits hg) fp
  return (parityHGAssignment hg blocks)

-- | Read and parse a partition file strictly, so the handle is closed before
--   the caller overwrites or removes the file.
readPartitionFile :: String -> Int -> Int -> FilePath -> IO [Int]
readPartitionFile context k n fp = do
  contents <- readFile fp
  _ <- evaluate (length contents)
  either (ioError . userError . ((context ++ ": ") ++)) return
         (parsePartition k n contents)

-- | Write an hMetis file, run KaHyPar on it and read back one block per vertex.
runKaHyPar :: Int -> Int -> String -> IO [Int]
runKaHyPar k n hmetis = do
  let dir      = Cfg.hypergraphPartitionDataPath
      graphFN  = "parity.hgr"
      graphFP  = dir </> graphFN
      partFP   = dir </> "parity.partition"
      isPart f = (graphFN ++ ".part") `isPrefixOf` f

  createDirectoryIfMissing True dir

  -- Remove partition files from earlier runs, so the one we read is fresh.
  old <- filter isPart <$> listDirectory dir
  forM_ old (removeFile . (dir </>))

  writeFile graphFP hmetis

  let args = [ "-h", graphFP
             , "-k", show k
             , "-e", show Cfg.epsilon
             , "-o", "km1"
             , "-m", "direct"
             , "-p", Cfg.subalgorithm
             , "-w", "true" ]
  (ec, out, err) <- readProcessWithExitCode Cfg.kahyparPath args ""
  case ec of
    ExitSuccess -> pure ()
    _ -> do
      hPutStrLn stderr $ "KaHyPar failed on the parity hypergraph.\n--- stdout ---\n" ++ out
                      ++ "\n--- stderr ---\n" ++ err
      ioError (userError "partitionParityHG: KaHyPar exited with an error.")

  -- KaHyPar names its output <graph>.part<k>.epsilon<e>.seed<s>.KaHyPar
  produced <- filter isPart <$> listDirectory dir
  partFile <- case produced of
    [f] -> pure (dir </> f)
    []  -> ioError (userError "partitionParityHG: KaHyPar did not produce a partition file.")
    fs  -> ioError (userError ("partitionParityHG: several partition files found: " ++ unwords fs))

  blocks <- readPartitionFile "partitionParityHG" k n partFile

  -- Keep a stable copy next to the other partition files, and remove
  -- KaHyPar's own output so 'getNumCuts' does not pick it up as its latest.
  writeFile partFP (unlines (map show blocks))
  removeFile partFile
  return blocks