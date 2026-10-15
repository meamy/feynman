module Feynman.Synthesis.HypergraphPartition.DistributedCircuitBuilder where
import Feynman.Core (Primitive(..), ID, Block, Vertex(..), PartitionData,
                     isZBasisPhaseGate, getArgs,
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
import Feynman.Synthesis.HypergraphPartition.CatStateOptimizer (fusePersistentCats, preservesZValue)

import Data.List (foldl', groupBy, intercalate, sortBy, sort)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad (foldM, when)
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

data EvaluatedSplit = EvaluatedSplit
  { evaluatedSource    :: String
  , evaluatedMap       :: Map Vertex Block
  , evaluatedCircuit   :: [Primitive]
  , evaluatedRawEbits  :: Int
  , evaluatedSaved     :: Int
  , evaluatedEbits     :: Int
  , evaluatedAlgebraic :: Int
  , evaluatedPredicted :: Int
  , evaluatedValid     :: Bool
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

synthPhases :: [ID] -> Int -> [Phase] -> Map F2Vec Int -> Map ID Int 
            -> Map Vertex Block -> ([Primitive], [ID])
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

distSynth :: [ID] -> F2Mat -> Int -> [Phase] -> Map F2Vec Int 
          -> Map ID Int -> Map Vertex Block -> ([Primitive], Int)
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

-- Reorder a chunk's linear transformation into QPU-0/QPU-1 wire order.
reorderForSplit :: [ID] -> [ID] -> F2Mat -> F2Mat
reorderForSplit ids ordered a =
  let positions = Map.fromList (zip ids [0 :: Int ..])
      reorderVec v = fromBits (reverse [v @. (positions Map.! q) | q <- ordered])
  in fromList [reorderVec (row a (positions Map.! q)) | q <- ordered]

phaseImportsForSplit :: [ID] -> [ID] -> ChunkSummary -> (Int, [((Int, Int), F2Vec)])
phaseImportsForSplit ids ids0 cs =
  (cost, tag 0 (importedBasis s0 mask0 mask1) ++ tag 1 (importedBasis s1 mask1 mask0))
  where
    side0          = Set.fromList ids0
    ordered        = ids0 ++ [q | q <- ids, Set.notMember q side0]
    (mask0, mask1) = splitMasks ordered ids0
    -- Synthesis reads parities from a Map keyed in 'ordered' coordinates.
    ps             = sort (map (reorderParity ids ordered) (chunkParities cs))
    (s0, s1, cost) = matroidPhaseSplit mask0 mask1 ps
    tag d          = zipWith (\i p -> ((d, i), reorderParity ordered ids p)) [0 ..]

-- Indices [start,end) of CNOT/Z-phase chunks in the ORIGINAL circuit.
phaseChunkBounds :: [Primitive] -> [(Int, Int)]
phaseChunkBounds circ =
  [ (start, start + length chunk)
  | (start, chunk) <- zip offsets chunks, isPP (head chunk) ]
  where
    isPP (CNOT _ _) = True
    isPP g = isZBasisPhaseGate g
    chunks = groupBy (\a b -> isPP a == isPP b) circ
    offsets = scanl (+) 0 (map length chunks)

sourceInvalidations :: [ID] -> [Primitive] -> Map ID (Set Int)
sourceInvalidations ids circ = foldl' visit initial (zip [0 :: Int ..] circ)
  where
    initial = Map.fromList [(q, Set.empty) | q <- ids]
    visit acc (i, gate) = foldl' (mark gate i) acc (getArgs gate)
    mark gate i acc q
      | Map.member q acc && not (preservesZValue q gate) =
          Map.adjust (Set.insert i) q acc
      | otherwise = acc

reorderParity :: [ID] -> [ID] -> F2Vec -> F2Vec
reorderParity ids ordered v =
  let positions = Map.fromList (zip ids [0 :: Int ..])
  in fromBits (reverse [v @. (positions Map.! q) | q <- ordered])


basisStableInOriginal :: [ID] -> Map ID (Set Int) -> Int -> Int -> F2Vec -> Bool
basisStableInOriginal ids invalidations lo hi basis =
  and [not (basis @. i) || noBarrier q
      | (i, q) <- zip [0 :: Int ..] ids]
  where
    noBarrier q =
      case Set.lookupGE lo (Map.findWithDefault Set.empty q invalidations) of
        Nothing -> True
        Just j -> j >= hi


predictedPersistenceSaving :: [ID] -> [ChunkSummary] -> [(Int, Int)] -> Map ID (Set Int) -> [ID] -> Int
predictedPersistenceSaving ids summaries bounds invalidations ids0 =
  fst $ foldl' step (0, Map.empty) (zip bounds summaries)
  where
    step (saved, previous) ((start, end), cs) =
      let (_, imports) = phaseImportsForSplit ids ids0 cs
          reusable (key, basis) =
            case Map.lookup key previous of
              Just (oldBasis, oldStart) ->
                oldBasis == basis &&
                basisStableInOriginal ids invalidations oldStart end basis
              Nothing -> False
          savedHere = length (filter reusable imports)
          previous' = foldl' (\acc (key, basis) ->
                                Map.insert key (basis, start) acc)
                            previous imports
      in (saved + savedHere, previous')

persistenceAwareSplitCost :: [ID] -> [ChunkSummary] -> [(Int, Int)] 
                          -> Map ID (Set Int) -> [ID] -> Int
persistenceAwareSplitCost ids summaries bounds invalidations ids0 =
  let raw = algebraicSplitCost ids summaries ids0
      saved = predictedPersistenceSaving ids summaries bounds invalidations ids0
  in max 0 (raw - saved)


lexicographicSplitScore :: [ID] -> [ChunkSummary] -> [(Int, Int)] 
                        -> Map ID (Set Int) -> [ID] -> (Int, Int)
lexicographicSplitScore ids summaries bounds invalidations ids0 =
  let raw = algebraicSplitCost ids summaries ids0
      reuse = predictedPersistenceSaving ids summaries bounds invalidations ids0
  in (raw, negate reuse)

persistenceScoreBreakdown :: [ID] -> [ChunkSummary] -> [(Int, Int)] 
                          -> Map ID (Set Int) -> [ID] -> (Int, Int, Int)
persistenceScoreBreakdown ids summaries bounds invalidations ids0 =
  let raw = algebraicSplitCost ids summaries ids0
      reuse = predictedPersistenceSaving ids summaries bounds invalidations ids0
  in (raw, reuse, max 0 (raw - reuse))

betterFinalist :: EvaluatedSplit -> EvaluatedSplit -> EvaluatedSplit
betterFinalist x y
  | evaluatedValid x && not (evaluatedValid y) = x
  | evaluatedValid y && not (evaluatedValid x) = y
  | evaluatedEbits x <= evaluatedEbits y = x
  | otherwise = y

-- Number of Bell pairs consumed by the CURRENT block-ULDU linear synthesis
linearCostAlgebraic :: [ID] -> [ID] -> F2Mat -> Int
linearCostAlgebraic ids ids0 finalMat =
  let side0   = Set.fromList ids0
      ids1    = [q | q <- ids, Set.notMember q side0]
      ordered = ids0 ++ ids1
      b       = reorderForSplit ids ordered finalMat
      n0      = length ids0
      sz      = m b
      (u, l, _, u2) = blockUlduFact b n0
      uBlock  = subMat u  (0, n0)  (n0, sz)
      lBlock  = subMat l  (n0, sz) (0, n0)
      u2Block = subMat u2 (0, n0)  (n0, sz)
  in rank uBlock + rank lBlock + rank u2Block

algebraicSplitCost :: [ID] -> [ChunkSummary] -> [ID] -> Int
algebraicSplitCost ids summaries ids0 = sum (map scoreChunk summaries)
  where
    (mask0, mask1) = splitMasks ids ids0
    scoreChunk cs =
      let (_, _, phaseEbits) = matroidPhaseSplit mask0 mask1 (chunkParities cs)
          linearEbits = linearCostAlgebraic ids ids0 (chunkFinal cs)
      in phaseEbits + linearEbits

-- Validate a candidate against the actual (non-persistent) synthesized cost.
validateAlgebraicSplitCost :: [Primitive] -> [ID] -> [ChunkSummary] -> [ID] -> Bool
validateAlgebraicSplitCost circ ids summaries ids0 =
  let side0 = Set.fromList ids0
      ids1  = [q | q <- ids, Set.notMember q side0]
  in algebraicSplitCost ids summaries ids0 ==
     snd (synthesizeUnderQubitSplit circ ids0 ids1)

{- Cost-specific search wrappers (the search itself lives in BeamSearch) -}
-- | Beam search with a synthesis-free score matching the raw ebit pipeline.
beamSearchQubitSplitAlgebraic :: [Primitive] -> Map ID Int -> Map Vertex Block
                              -> Double -> Int -> Int -> (Map Vertex Block, Int)
beamSearchQubitSplitAlgebraic circ qIndexMap seed = beamSearchWith score seed
  where
    ids       = Map.keys qIndexMap
    summaries = summarizeChunks ids circ
    score pm  = algebraicSplitCost ids summaries
                  (fst (splitOfPartMap qIndexMap pm))

exhaustiveQubitSplitAlgebraic :: [Primitive] -> Map ID Int -> Map Vertex Block
                              -> Double -> (Map Vertex Block, Int)
exhaustiveQubitSplitAlgebraic circ qIndexMap seed = exhaustiveSearchWith score seed
  where
    ids       = Map.keys qIndexMap
    summaries = summarizeChunks ids circ
    score pm  = algebraicSplitCost ids summaries
                  (fst (splitOfPartMap qIndexMap pm))

-- | Algebraic beam search: minimize RAW cost first; prefer predicted
beamSearchQubitSplitPersistenceTieBreak :: [Primitive] -> Map ID Int -> Map Vertex Block 
                                        -> Double -> Int -> Int -> (Map Vertex Block, (Int, Int))
beamSearchQubitSplitPersistenceTieBreak circ qIndexMap seed =
  beamSearchWithLexicographic score seed
  where
    ids = Map.keys qIndexMap
    summaries = summarizeChunks ids circ
    bounds = phaseChunkBounds circ
    invalidations = sourceInvalidations ids circ
    score pm = lexicographicSplitScore ids summaries bounds invalidations
                 (fst (splitOfPartMap qIndexMap pm))

-- | Small-circuit exhaustive version, again with algebra-only scoring.
exhaustiveQubitSplitPersistenceTieBreak :: [Primitive] -> Map ID Int -> Map Vertex Block 
                                        -> Double -> (Map Vertex Block, (Int, Int))
exhaustiveQubitSplitPersistenceTieBreak circ qIndexMap seed =
  exhaustiveSearchWithLexicographic score seed
  where
    ids = Map.keys qIndexMap
    summaries = summarizeChunks ids circ
    bounds = phaseChunkBounds circ
    invalidations = sourceInvalidations ids circ
    score pm = lexicographicSplitScore ids summaries bounds invalidations
                 (fst (splitOfPartMap qIndexMap pm))

-- buildDistributedCircuit :: Int -> [ID] -> [Primitive] -> IO [Primitive]
-- buildDistributedCircuit numParts qubits circ
--   | numParts /= 2 = ioError . userError $
--       "buildDistributedCircuit: supports exactly 2 QPUs, got " ++ show numParts
--   | otherwise = do
--       let
--           -- Knobs.
--           useBeamSearch   = True    
--           useQIGSeed      = False   
--           eps             = Cfg.epsilon
--           beamWidth       = 8
--           depth           = 14
--           exactSplitLimit = 12     
--           validateScore   = False  
--           showSteps       = False

--           n         = length qubits
--           half      = (n + 1) `div` 2
--           qIndexMap = Map.fromList (zip qubits [1 ..])

--           -- Naive split: wires 1..half (declared order) on QPU 0, the rest on QPU 1.
--           naiveSeed = Map.fromList [ (Wire w, if w <= half then 0 else 1) | w <- [1 .. n] ]

--       seedMap <-
--         if useQIGSeed
--         then do
--           (_, asg) <- QIG.partitionQIG 2 qubits circ
--           return $ Map.fromList [ (Wire w, b) | (q, b) <- Map.toList asg
--                                               , Just w <- [Map.lookup q qIndexMap] ]
--         else return naiveSeed

--       let
--           -- Score of a split without searching (same score the beam uses).
--           ids        = Map.keys qIndexMap
--           summaries  = summarizeChunks ids circ
--           scoreOf pm = algebraicSplitCost ids summaries (fst (splitOfPartMap qIndexMap pm))

--           (bestMap, searchScore)
--             | not useBeamSearch    = (seedMap, scoreOf seedMap)
--             | n <= exactSplitLimit = exhaustiveSearchWith scoreOf seedMap eps
--             | otherwise            = beamSearchWith scoreOf seedMap eps beamWidth depth

--           (ids0, ids1) = splitOfPartMap qIndexMap bestMap

--           partitions = Map.fromList
--                          ([ (q, 0) | q <- ids0 ] ++ [ (q, 1) | q <- ids1 ])

--           (distributedCirc, totalEbits) = synthesizeUnderQubitSplit circ ids0 ids1

--           seedName   = if useQIGSeed then "QIG" else "naive equal split"
--           searchName
--             | not useBeamSearch    = "no search"
--             | n <= exactSplitLimit = "exhaustive search"
--             | otherwise            = "beam search"
--           scoreName = "Edmonds phase + exact ULDU ranks (no synthesis in search)"

--       -- reportInputParities qubits circ
--       reportDist $ "Qubit assignment: " ++ searchName ++ " from " ++ seedName
--       reportDist $ "QPU 0 (" ++ show (length ids0) ++ " qubits): " ++ unwords (sortBy compare ids0)
--       reportDist $ "QPU 1 (" ++ show (length ids1) ++ " qubits): " ++ unwords (sortBy compare ids1)
--       when showSteps $ reportSynthesisSteps circ ids0 ids1
--       reportDist $ "Search score (" ++ scoreName ++ "): " ++ show searchScore
--       when validateScore $
--         reportDist $ "Algebraic score validation: " ++
--                      (if searchScore == totalEbits then "PASS" else "MISMATCH")
--       reportDist $ "Ebit cost: " ++ show totalEbits
--       reportDist $ "Distribution: " ++ (if verifyDist distributedCirc partitions
--                                       then "PASS"
--                                       else "FAILED (cross-partition gate)")

--       return distributedCirc


buildDistributedCircuit :: Int -> [ID] -> [Primitive] -> IO [Primitive]
buildDistributedCircuit numParts qubits circ
  | numParts /= 2 = ioError . userError $
      "buildDistributedCircuit: supports exactly 2 QPUs, got " ++ show numParts
  | otherwise = do
      let
          -- Knobs.
          useBeamSearch        = True
          useQIGSeed           = False
          eps                  = Cfg.epsilon
          beamWidth            = 8
          depth                = 14
          exactSplitLimit      = 8      -- exhaustive algebraic for small circuits
          compareRawBaseline   = True   -- safeguard: compare up to TWO finalists
          validateScore        = True   -- raw algebraic vs raw synth on finalists

          n         = length qubits
          half      = (n + 1) `div` 2
          qIndexMap = Map.fromList (zip qubits [1 ..])
          naiveSeed = Map.fromList
            [(Wire w, if w <= half then 0 else 1) | w <- [1 .. n]]

      seedMap <-
        if useQIGSeed
        then do
          (_, asg) <- QIG.partitionQIG 2 qubits circ
          return $ Map.fromList
            [(Wire w, b) | (q, b) <- Map.toList asg
                         , Just w <- [Map.lookup q qIndexMap]]
        else return naiveSeed

      let
          ids           = Map.keys qIndexMap
          summaries     = summarizeChunks ids circ
          bounds        = phaseChunkBounds circ
          invalidations = sourceInvalidations ids circ

          -- Both scores operate on algebraic summaries; neither synthesizes.
          rawScoreOf pm =
            algebraicSplitCost ids summaries (fst (splitOfPartMap qIndexMap pm))
          tieScoreOf pm =
            lexicographicSplitScore ids summaries bounds invalidations
              (fst (splitOfPartMap qIndexMap pm))

          -- This is the ORIGINAL (12-ebit benchmark) ranking, unchanged.
          (baselineMap, baselineScore)
            | not useBeamSearch = (seedMap, rawScoreOf seedMap)
            | n <= exactSplitLimit =
                exhaustiveQubitSplitAlgebraic circ qIndexMap seedMap eps
            | otherwise =
                beamSearchQubitSplitAlgebraic circ qIndexMap seedMap
                                              eps beamWidth depth

          -- Persistence predicts only tie order. Raw algebraic cost is ALWAYS
          -- the first element of the ordering pair (raw, -predictedSaving).
          (tieMap, tieScore)
            | not useBeamSearch = (seedMap, tieScoreOf seedMap)
            | n <= exactSplitLimit =
                exhaustiveQubitSplitPersistenceTieBreak circ qIndexMap seedMap eps
            | otherwise =
                beamSearchQubitSplitPersistenceTieBreak circ qIndexMap seedMap
                                                        eps beamWidth depth

          -- Preserve the baseline in case the tie-aware beam follows a worse
          -- route. When both searches choose the same map, synthesize once.
          finalists
            | not compareRawBaseline || baselineMap == tieMap =
                [("persistence tie-break", tieMap)]
            | otherwise =
                [("raw-algebraic baseline", baselineMap),
                 ("persistence tie-break", tieMap)]

          evaluateFinalist (origin, pm) =
            let (ids0, ids1) = splitOfPartMap qIndexMap pm
                partitions = Map.fromList
                  ([(q, 0) | q <- ids0] ++ [(q, 1) | q <- ids1])
                (rawPredicted, reusePredicted, _) =
                  persistenceScoreBreakdown ids summaries bounds invalidations ids0
                -- Finalists only: this is NEVER called by a beam score.
                (rawCirc, rawEbits) = synthesizeUnderQubitSplit circ ids0 ids1
                (optCirc, saved) = fusePersistentCats rawCirc
                total = max 0 (rawEbits - saved)
            in EvaluatedSplit
                 { evaluatedSource = origin
                 , evaluatedMap = pm
                 , evaluatedCircuit = optCirc
                 , evaluatedRawEbits = rawEbits
                 , evaluatedSaved = saved
                 , evaluatedEbits = total
                 , evaluatedAlgebraic = rawPredicted
                 , evaluatedPredicted = reusePredicted
                 , evaluatedValid = verifyDist optCirc partitions
                 }

          evaluated = map evaluateFinalist finalists
          winner = foldl1 betterFinalist evaluated
          (ids0, ids1) = splitOfPartMap qIndexMap (evaluatedMap winner)

          seedName = if useQIGSeed then "QIG" else "naive equal split"
          searchName
            | not useBeamSearch = "no search"
            | n <= exactSplitLimit = "exhaustive search"
            | otherwise = "beam search"

      reportDist $ "Qubit assignment: " ++ searchName ++ " from " ++ seedName
      reportDist $ "Search objective: lexicographic (Edmonds + ULDU, -predicted reuse)"
      reportDist $ "Raw baseline search score: " ++ show baselineScore
      reportDist $ "Tie-break search score (raw, -reuse): " ++ show tieScore
      reportDist $ "Finalists synthesized after search: " ++ show (length finalists)
      mapM_ (\e -> do
        reportDist $ "  Finalist " ++ evaluatedSource e ++
                     ": algebraic=" ++ show (evaluatedAlgebraic e) ++
                     ", predicted reuse=" ++ show (evaluatedPredicted e) ++
                     ", actual saved=" ++ show (evaluatedSaved e) ++
                     ", actual ebits=" ++ show (evaluatedEbits e) ++
                     ", distribution=" ++ (if evaluatedValid e then "PASS" else "FAILED")
        when validateScore $
          reportDist $ "    Algebraic-vs-raw-synthesis: " ++
            (if evaluatedAlgebraic e == evaluatedRawEbits e
             then "PASS" else "MISMATCH")) evaluated

      reportDist $ "Selected finalist: " ++ evaluatedSource winner
      reportDist $ "QPU 0 (" ++ show (length ids0) ++ " qubits): " ++
                   unwords (sortBy compare ids0)
      reportDist $ "QPU 1 (" ++ show (length ids1) ++ " qubits): " ++
                   unwords (sortBy compare ids1)
      reportDist $ "Raw algebraic cost: " ++ show (evaluatedAlgebraic winner)
      reportDist $ "Predicted persistence saving (tie-break only): " ++
                   show (evaluatedPredicted winner)
      reportDist $ "Actual fusion saving: " ++ show (evaluatedSaved winner)
      reportDist $ "Ebit cost: " ++ show (evaluatedEbits winner)
      reportDist $ "Distribution: " ++
                   (if evaluatedValid winner then "PASS" else "FAILED (cross-partition gate)")

      return (evaluatedCircuit winner)