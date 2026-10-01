module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where
import Feynman.Core (Primitive(..), ID, Block, Vertex(..), PartitionData,
                     isZBasisPhaseGate,
                     catEntangler, catDisentangler,
                     catEntanglerMulti, catDisentanglerMulti)
import Feynman.Algebra.Linear
import Feynman.Algebra.Matroid (matroidIntersection)
import Feynman.Synthesis.Reversible (Phase, LinearTrans, linearSynth)
import qualified Feynman.Synthesis.Reversible.Gray as Gray
import Feynman.Optimization.TPar (AnalysisState(..), applyGate)

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import qualified Feynman.Synthesis.HypergraphPartition.QIGBuilder as QIG
import Feynman.Synthesis.HypergraphPartition.BeamSearch
import Feynman.Synthesis.HypergraphPartition.CatStateOptimizer (fusePersistentCats)

import Data.List (foldl', groupBy, intercalate, sortBy)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad (foldM)
import Control.Monad.State.Strict (runState)

import Data.IORef (IORef, newIORef, modifyIORef', atomicModifyIORef')
import System.IO.Unsafe (unsafePerformIO)


data ChunkSummary = ChunkSummary
  { 
     -- phase parities, bit i <-> ids !! i
    chunkParities :: [F2Vec],
     -- linear map B, row i = image of ids !! i
    chunkFinal    :: F2Mat

  }

{-# NOINLINE distReport #-}
distReport :: IORef [String]
distReport = unsafePerformIO (newIORef [])

-- Record one line of the distribution report.
reportDist :: String -> IO ()
reportDist line = modifyIORef' distReport (++ [line])

-- Take the recorded lines, clearing them for the next run.
takeDistReport :: IO [String]
takeDistReport = atomicModifyIORef' distReport (\ls -> ([], ls))

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

synthDistributedLinear :: [ID] -> F2Mat -> Int -> [Primitive]
synthDistributedLinear ids a n =
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

  in  gatesU2 ++ gatesD0 ++ gatesD1 ++ gatesL ++ gatesU

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
  in
      -- trace debugMsg
      ( entanglers0 ++ grayGates0 ++ disentanglers0 ++
        entanglers1 ++ grayGates1 ++ disentanglers1
      , allBells0 ++ allBells1
      )

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

distSynth :: [ID] -> F2Mat -> Int -> [Phase] -> Map F2Vec Int -> Map ID Int -> Map Vertex Block -> ([Primitive], Int)
distSynth ids finalMat numQPUs phases parityToPart qIndexMap partMap =
  let
    (phaseGates, phaseBells) = synthPhases ids numQPUs phases parityToPart qIndexMap partMap
    rawLinearGates = synthDistributedLinear ids finalMat numQPUs

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

{- Helpers for usage of matroid intersection-}
matroidPhaseSplit :: F2Vec -> F2Vec -> [F2Vec] -> ([F2Vec], [F2Vec], Int)
matroidPhaseSplit mask0 mask1 parities = (s0, s1, Set.size common)
  where
    -- Work over indices so that parities with equal projections stay
    -- distinct elements of the ground set (they are parallel, not equal).
    byIdx  = Map.fromList (zip [0 :: Int ..] parities)
    ground = Map.keysSet byIdx

    proj mask i = (byIdx Map.! i) * mask

    indepBy mask s
      | Set.null s = True
      | otherwise  = let vs = map (proj mask) (Set.toList s)
                     in rank (fromList vs) == length vs

    -- M1 = QPU-1 projections (what QPU 0 must import),
    -- M2 = QPU-0 projections (what QPU 1 must import).
    (common, reachable, _) = matroidIntersection ground (indepBy mask1) (indepBy mask0)

    side i
      | wt (proj mask1 i) == 0   = 0 :: Int
      | wt (proj mask0 i) == 0   = 1
      | Set.member i reachable   = 1
      | otherwise                = 0

    s0 = [ byIdx Map.! i | i <- Set.toList ground, side i == 0 ]
    s1 = [ byIdx Map.! i | i <- Set.toList ground, side i == 1 ]

synthDistributedMatroid :: [ID] -> Int -> LinearTrans -> [Phase] -> ([Primitive], Int)
synthDistributedMatroid ids numQpu0 outB phases =
  let n     = length ids
      mask0 = fromBits (reverse [ i <  numQpu0 | i <- [0 .. n - 1] ])
      mask1 = fromBits (reverse [ i >= numQpu0 | i <- [0 .. n - 1] ])

      (s0, s1, _)  = matroidPhaseSplit mask0 mask1 (map fst phases)
      parityToPart = Map.fromList ([ (p, 0) | p <- s0 ] ++ [ (p, 1) | p <- s1 ])

      finalMat = fromList [ outB Map.! q | q <- ids ]

      -- The (ids, numQpu0) split in the Map form distSynth expects.
      localQIdx = Map.fromList (zip ids [1 ..])
      localPart = Map.fromList [ (Wire i, if i <= numQpu0 then 0 else 1) | i <- [1 .. n] ]
  in distSynth ids finalMat numQpu0 phases parityToPart localQIdx localPart

synthesizeUnderQubitSplit :: [Primitive] -> [ID] -> [ID] -> ([Primitive], Int)
synthesizeUnderQubitSplit circ ids0 ids1 =
  let sortedIds = ids0 ++ ids1
      numQpu0   = length ids0
      n         = length sortedIds

      isPP (CNOT _ _) = True
      isPP g | isZBasisPhaseGate g = True
      isPP _ = False

      chunks = groupBy (\g1 g2 -> isPP g1 == isPP g2) circ

      -- Consecutive CNOT/phase gates always land in one chunk, so every such
      -- chunk starts from a non-PP chunk (or the circuit start): its input
      -- is the identity, which is why no A matrix is needed.

      processChunk (accCirc, accEbits) chunk
        | not (isPP (head chunk)) = (accCirc ++ chunk, accEbits)
        | otherwise =
            let (phases, finalMat) = extractPhasesAndMatrix sortedIds chunk (identity n)
                outB               = Map.fromList (zip sortedIds (toList finalMat))
                (gates, ebits)     = synthDistributedMatroid sortedIds numQpu0 outB phases
            in (accCirc ++ gates, accEbits + ebits)
  in foldl' processChunk ([], 0) chunks


synthesizeUnderPartition :: [Primitive] -> Map ID Int -> Map Vertex Block -> ([Primitive], Int)     
synthesizeUnderPartition circ qIndexMap partMap =
  let getPart wIdx = Map.findWithDefault 0 (Wire wIdx) partMap

      idPartitions = [ (qid, getPart wIdx) | (qid, wIdx) <- Map.toList qIndexMap ]
      ids0 = [ qid | (qid, part) <- idPartitions, part == 0 ]
      ids1 = [ qid | (qid, part) <- idPartitions, part == 1 ]

      sortedIds = ids0 ++ ids1
      numQpu0   = length ids0

      origQubits = map fst $ sortBy (comparing snd) $ Map.toList qIndexMap
      origParities = HG.extractParities origQubits circ
      n = length origQubits

      translateParity p =
        let activeQs = [ origQubits !! k | k <- [0..n-1], p @. k ]
            bools = [ (sortedIds !! i) `elem` activeQs | i <- [0..n-1] ]
        in fromBits (reverse bools)

      translatedParities = map translateParity origParities

      parityToPart = Map.fromList [ (tp, Map.findWithDefault 0 (GateIdx (n + 1 + j)) partMap)
                                  | (tp, j) <- zip translatedParities [0..] ]

      isPP (CNOT _ _) = True
      isPP g | isZBasisPhaseGate g = True
      isPP _ = False

      chunks = groupBy (\g1 g2 -> isPP g1 == isPP g2) circ

      initialMat = identity n

      processChunk :: ([Primitive], F2Mat, Int) -> [Primitive] -> ([Primitive], F2Mat, Int)
      processChunk (accCirc, currentMat, accEbits) chunk
        | null chunk = (accCirc, currentMat, accEbits)
        | not (isPP (head chunk)) =
            (accCirc ++ chunk, identity n, accEbits)
        | otherwise =
            let (phases, finalMat) = extractPhasesAndMatrix sortedIds chunk currentMat
                (synths, chunkEbits) = distSynth sortedIds finalMat numQpu0 phases parityToPart qIndexMap partMap
            in (accCirc ++ synths, finalMat, accEbits + chunkEbits)

      (distributedCirc, _, totalEbits) = foldl' processChunk ([], initialMat, 0) chunks
  in (distributedCirc, totalEbits)

-- Convenience: score only (ebit cost) for a candidate partition.
scorePartition :: [Primitive] -> Map ID Int -> Map Vertex Block -> Int
scorePartition circ qIndexMap partMap = snd (synthesizeUnderPartition circ qIndexMap partMap)

splitOfPartMap :: Map ID Int -> Map Vertex Block -> ([ID], [ID])
splitOfPartMap qIndexMap pm = (ids0, ids1)
  where
    blockOf q = Map.findWithDefault 0 (Wire (Map.findWithDefault 0 q qIndexMap)) pm
    assigned  = [ (q, blockOf q) | q <- Map.keys qIndexMap ]
    ids0      = [ q | (q, b) <- assigned, b == 0 ]
    ids1      = [ q | (q, b) <- assigned, b /= 0 ]


-- | Exact ebit cost of a split: synthesizes the circuit and counts.
scoreQubitSplit :: [Primitive] -> Map ID Int -> Map Vertex Block -> Int
scoreQubitSplit circ qIndexMap pm =
  let (ids0, ids1) = splitOfPartMap qIndexMap pm
  in snd (synthesizeUnderQubitSplit circ ids0 ids1)

-- | Summarize every CNOT/phase chunk once, in the given qubit order.
summarizeChunks :: [ID] -> [Primitive] -> [ChunkSummary]
summarizeChunks ids circ =
  [ summarize chunk | chunk <- chunks, isPP (head chunk) ]
  where
    n = length ids

    isPP (CNOT _ _) = True
    isPP g | isZBasisPhaseGate g = True
    isPP _ = False

    chunks = groupBy (\g1 g2 -> isPP g1 == isPP g2) circ

    summarize chunk =
      let (phases, finalMat) = extractPhasesAndMatrix ids chunk (identity n)
      in ChunkSummary { chunkParities = map fst phases, chunkFinal = finalMat }

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


-- QPU-0 and QPU-1 masks for a split, over the fixed qubit order.
splitMasks :: [ID] -> [ID] -> (F2Vec, F2Vec)
splitMasks ids ids0 = (fromBits (reverse onQpu0), fromBits (reverse (map not onQpu0)))
  where onQpu0 = [ q `elem` ids0 | q <- ids ]

-- Estimated ebit cost of a split, from the matroid value per chunk.
-- phaseOnly drops the linear estimate, leaving the pure matroid value.
estimateSplitCost :: Bool -> [ID] -> [ChunkSummary] -> [ID] -> Int
estimateSplitCost phaseOnly ids summaries ids0 = sum (map chunkScore summaries)
  where
    (mask0, mask1) = splitMasks ids ids0

    chunkScore cs = phaseCost cs + (if phaseOnly then 0 else linearCost cs)

    -- Exact: matroid intersection gives the optimal phase cost directly.
    phaseCost cs =
      let (_, _, c) = matroidPhaseSplit mask0 mask1 (chunkParities cs) in c

    -- Estimate: ranks of the two off-diagonal blocks of B.
    linearCost cs =
      let rowsOn side mask = [ v * mask
                             | (q, v) <- zip ids (toList (chunkFinal cs))
                             , (q `elem` ids0) == side ]
          rk vs = if null vs then 0 else rank (fromList vs)
      in rk (rowsOn True mask1) + rk (rowsOn False mask0)

-- Preserve the old chunked synthesis as the base implementation, then optimize
-- its communication schedule across chunk boundaries.
synthesizeUnderQubitSplitPersistent :: [Primitive] -> [ID] -> [ID] -> ([Primitive], Int)
synthesizeUnderQubitSplitPersistent circ ids0 ids1 =
  let (rawCirc, rawEbits) = synthesizeUnderQubitSplit circ ids0 ids1
      (optCirc, saved)     = fusePersistentCats rawCirc
  in (optCirc, max 0 (rawEbits - saved))

scoreQubitSplitPersistent :: [Primitive] -> Map ID Int -> Map Vertex Block -> Int
scoreQubitSplitPersistent circ qIndexMap pm =
  let (ids0, ids1) = splitOfPartMap qIndexMap pm
  in snd (synthesizeUnderQubitSplitPersistent circ ids0 ids1)

{- Cost-specific search wrappers (the search itself lives in BeamSearch) -}

-- | Beam search scored by the vanilla pipeline (KaHyPar parity blocks).
beamSearchPartition :: [Primitive] -> Map ID Int -> Map Vertex Block
                    -> Double -> Int -> Int -> (Map Vertex Block, Int)
beamSearchPartition circ qIndexMap = beamSearchWith (scorePartition circ qIndexMap)

-- | Beam search on the exact cost. Correct, but synthesizes once per candidate.
beamSearchQubitSplit :: [Primitive] -> Map ID Int -> Map Vertex Block
                     -> Double -> Int -> Int -> (Map Vertex Block, Int)
beamSearchQubitSplit circ qIndexMap = beamSearchWith (scoreQubitSplit circ qIndexMap)

-- | Beam search on the estimate. Chunks are summarized once, up front.
beamSearchQubitSplitFast :: Bool -> [Primitive] -> Map ID Int -> Map Vertex Block
                         -> Double -> Int -> Int -> (Map Vertex Block, Int)
beamSearchQubitSplitFast phaseOnly circ qIndexMap seed =
  beamSearchWith score seed
  where
    ids       = Map.keys qIndexMap
    summaries = summarizeChunks ids circ
    score pm  = estimateSplitCost phaseOnly ids summaries (fst (splitOfPartMap qIndexMap pm))

-- Exact search under the persistent-cat cost model.  This is intentionally used
-- for small circuits: it removes beam-pruning/tie-order effects entirely.
exhaustiveQubitSplitPersistent :: [Primitive] -> Map ID Int -> Map Vertex Block
                              -> Double -> (Map Vertex Block, Int)
exhaustiveQubitSplitPersistent circ qIndexMap =
  exhaustiveSearchWith (scoreQubitSplitPersistent circ qIndexMap)

-- Beam-search fallback for larger circuits. the pruning score is the cost of the circuit 
-- after persistent-cat fusion, so search and final synthesis optimize the same objective.
beamSearchQubitSplitPersistent :: [Primitive] -> Map ID Int -> Map Vertex Block
                               -> Double -> Int -> Int -> (Map Vertex Block, Int)
beamSearchQubitSplitPersistent circ qIndexMap =
  beamSearchWith (scoreQubitSplitPersistent circ qIndexMap)

buildDistributedCircuit :: Int -> [ID] -> [Primitive] -> IO [Primitive]
buildDistributedCircuit numParts qubits circ
  | numParts /= 2 = ioError . userError $
      "buildDistributedCircuit: supports exactly 2 QPUs, got " ++ show numParts
  | otherwise = do
      let
          useBeamSearch = True

          n         = length qubits
          half      = (n + 1) `div` 2
          qIndexMap = Map.fromList (zip qubits [1 ..])

          -- Wires 1..half on QPU 0, the rest on QPU 1.
      (_, asg) <- QIG.partitionQIG 2 qubits circ
      let 
          seedMap = Map.fromList [ (Wire w, b) | (q, b) <- Map.toList asg
                                         , Just w <- [Map.lookup q qIndexMap] ]
          -- seedMap = Map.fromList
          --             [ (Wire w, if w <= half then 0 else 1) | w <- [1 .. n] ]

          -- Beam search knobs.
          eps       = Cfg.epsilon
          beamWidth = 8
          depth     = 14
          exactSplitLimit = 12
          phaseOnly = False
         
          -- Search on the estimate (no synthesis per candidate), then
          -- synthesize the winner once. Swap in beamSearchQubitSplit to
          -- search on the exact cost instead.
          (ids0, ids1)
            | useBeamSearch = splitOfPartMap qIndexMap bestMap
            | otherwise     = splitAt half qubits
            where (bestMap, _estBest) =
                    beamSearchQubitSplitFast phaseOnly circ qIndexMap seedMap eps beamWidth depth
          -- (ids0, ids1)
          --   | useBeamSearch = splitOfPartMap qIndexMap bestMap
          --   | otherwise     = splitAt half qubits
          --   where (bestMap, _estBest) =
          --           if n <= exactSplitLimit
          --           then exhaustiveQubitSplitPersistent circ qIndexMap seedMap eps
          --           else beamSearchQubitSplitPersistent circ qIndexMap seedMap eps beamWidth depth

          partitions = Map.fromList
                         ([ (q, 0) | q <- ids0 ] ++ [ (q, 1) | q <- ids1 ])

          (distributedCirc, totalEbits) = synthesizeUnderQubitSplit circ ids0 ids1

      reportInputParities qubits circ
      reportDist $ "Qubit assignment: " ++ (if useBeamSearch then "beam search" else "vanilla (declared order)")
      reportDist $ "QPU 0 (" ++ show (length ids0) ++ " qubits): " ++ unwords (sortBy compare ids0)
      reportDist $ "QPU 1 (" ++ show (length ids1) ++ " qubits): " ++ unwords (sortBy compare ids1)
      reportDist $ "Ebit cost: " ++ show totalEbits
      reportDist $ "Distribution: " ++ (if verifyDist distributedCirc partitions
                                      then "PASS"
                                      else "FAILED (cross-partition gate)")

      return distributedCirc