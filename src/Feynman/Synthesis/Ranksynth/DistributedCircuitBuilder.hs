module Feynman.Synthesis.Ranksynth.DistributedCircuitBuilder
  ( module Feynman.Synthesis.Ranksynth.DistributedCircuitBuilder
  , module Feynman.Synthesis.Ranksynth.DistributedSynthesis
  , module Feynman.Synthesis.Ranksynth.Report
  ) where
import Feynman.Core (Primitive(..), ID, Block, Vertex(..),
                     isZBasisPhaseGate, getArgs)
import Feynman.Algebra.Linear

import qualified Feynman.Synthesis.HypergraphPartition.PartitionConfigs as Cfg
import qualified Feynman.Synthesis.HypergraphPartition.HGraphBuilder as HG
import qualified Feynman.Synthesis.HypergraphPartition.QIGBuilder as QIG
import Feynman.Synthesis.Ranksynth.BeamSearch
import Feynman.Synthesis.Ranksynth.CatStateOptimizer (fusePersistentCats, preservesZValue)
import Feynman.Synthesis.Ranksynth.DistributedSynthesis
import Feynman.Synthesis.Ranksynth.Report

import Data.List (foldl', groupBy, sort)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad (when)

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
beamSearchQubitSplitPersistenceTieBreak circ qIndexMap seed eps beamWidth depth =
  let (pm, s, _) = prunedBeamSearch cfg allWiresMovable score seed
  in (pm, s)
  where
    cfg = BeamConfig { bcEpsilon = eps, bcWidth = beamWidth, bcMaxDepth = depth
                     , bcPatience = Nothing, bcMaxSwaps = 400 }
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

{- Cat Fusion Optimizer -}
-- | Actual ebits of a split after cat fusion, and the raw (pre-fusion) count.
-- Same pipeline evaluateFinalist runs, so the score is exact.
fusedSplitCost :: [Primitive] -> [ID] -> [ID] -> (Int, Int)
fusedSplitCost circ ids0 ids1 =
  let (rawCirc, rawEbits) = synthesizeUnderQubitSplit circ ids0 ids1
      (_, saved)          = fusePersistentCats rawCirc
  in (max 0 (rawEbits - saved), rawEbits)

-- | Lexicographic: fewest ebits after fusion first; on ties prefer fewer raw
-- ebits (the split that relies less on fusion).
fusedSplitScore :: [Primitive] -> Map ID Int -> Map Vertex Block -> (Int, Int)
fusedSplitScore circ qIndexMap pm =
  let (ids0, ids1) = splitOfPartMap qIndexMap pm
  in fusedSplitCost circ ids0 ids1

beamSearchQubitSplitFused :: [Primitive] -> Map ID Int -> Map Vertex Block
                          -> Double -> Int -> Int -> Maybe Int
                          -> (Map Vertex Block, (Int, Int), SearchStats)
beamSearchQubitSplitFused circ qIndexMap seed eps beamWidth depth patience =
  prunedBeamSearch cfg allWiresMovable (fusedSplitScore circ qIndexMap)
                   (repairBalance eps seed)
  where
    cfg = BeamConfig { bcEpsilon = eps , bcWidth = beamWidth , bcMaxDepth = depth
                    ,bcPatience = patience
                    , bcMaxSwaps = 400 }

exhaustiveQubitSplitFused :: [Primitive] -> Map ID Int -> Map Vertex Block
                          -> Double -> (Map Vertex Block, (Int, Int))
exhaustiveQubitSplitFused circ qIndexMap =
  exhaustiveSearchWithLexicographic (fusedSplitScore circ qIndexMap)


{- Split-search strategies -}
data SplitStrategy
  = AlgebraicSearch
  | PersistenceTieBreakSearch
  | FusedSearch
  deriving (Show, Eq, Enum, Bounded)

-- | Knobs shared by all strategies. A knob a strategy does not use is ignored.
data SplitSearchSettings = SplitSearchSettings
  { ssUseBeamSearch      :: Bool
  , ssUseQIGSeed         :: Bool
  , ssEpsilon            :: Double
  , ssBeamWidth          :: Int
  , ssDepth              :: Int
  , ssExactSplitLimit    :: Int        -- exhaustive search when n <= this
  , ssPatience           :: Maybe Int  -- Algebraic/Fused beam: stop after k idle rounds
  , ssCompareRawBaseline :: Bool       -- PersistenceTieBreak: also synthesize the raw baseline
  , ssValidateScore      :: Bool
  , ssShowSteps          :: Bool
  }

defaultSplitSearchSettings :: SplitSearchSettings
defaultSplitSearchSettings = SplitSearchSettings
  { ssUseBeamSearch      = True
  , ssUseQIGSeed         = False
  , ssEpsilon            = Cfg.epsilon
  , ssBeamWidth          = 8
  , ssDepth              = 14
  , ssExactSplitLimit    = 8
  , ssPatience           = Nothing
  , ssCompareRawBaseline = True
  , ssValidateScore      = False
  , ssShowSteps          = False
  }

-- | Everything every strategy needs: the circuit, its wire numbering and the seed split.
data SplitProblem = SplitProblem
  { spQubits :: [ID]
  , spCirc   :: [Primitive]
  , spQIndex :: Map ID Int
  , spSeed   :: Map Vertex Block
  }

mkSplitProblem :: SplitSearchSettings -> [ID] -> [Primitive] -> IO SplitProblem
mkSplitProblem s qubits circ = do
  let n         = length qubits
      half      = (n + 1) `div` 2
      qIndexMap = Map.fromList (zip qubits [1 ..])
      -- Naive split: wires 1..half (declared order) on QPU 0, the rest on QPU 1.
      naiveSeed = Map.fromList [ (Wire w, if w <= half then 0 else 1) | w <- [1 .. n] ]
  seedMap <-
    if ssUseQIGSeed s
    then do
      (_, asg) <- QIG.partitionQIG 2 qubits circ
      return $ Map.fromList [ (Wire w, b) | (q, b) <- Map.toList asg
                                          , Just w <- [Map.lookup q qIndexMap] ]
    else return naiveSeed
  return SplitProblem { spQubits = qubits, spCirc = circ
                      , spQIndex = qIndexMap, spSeed = seedMap }

{- Shared reporting helpers -}

seedLabel :: SplitSearchSettings -> String
seedLabel s = if ssUseQIGSeed s then "QIG" else "naive equal split"

searchModeLabel :: SplitSearchSettings -> Int -> String
searchModeLabel s n
  | not (ssUseBeamSearch s)  = "no search"
  | n <= ssExactSplitLimit s = "exhaustive search"
  | otherwise                = "beam search"

partitionsOf :: [ID] -> [ID] -> Map ID Int
partitionsOf ids0 ids1 = Map.fromList ([ (q, 0) | q <- ids0 ] ++ [ (q, 1) | q <- ids1 ])

{- Strategy 1: algebraic score, no fusion -}
runAlgebraicSearch :: SplitSearchSettings -> SplitProblem -> IO [Primitive]
runAlgebraicSearch s sp = do
  let circ      = spCirc sp
      qIndexMap = spQIndex sp
      seedMap   = spSeed sp
      n         = length (spQubits sp)
      eps       = ssEpsilon s

      -- Score of a split without searching (same score the beam uses).
      ids        = Map.keys qIndexMap
      summaries  = summarizeChunks ids circ
      scoreOf pm = algebraicSplitCost ids summaries (fst (splitOfPartMap qIndexMap pm))
      cfg = BeamConfig { bcEpsilon = eps, bcWidth = ssBeamWidth s, bcMaxDepth = ssDepth s
                       , bcPatience = ssPatience s, bcMaxSwaps = 400 }
      (bestMap, searchScore)
        | not (ssUseBeamSearch s)  = (seedMap, scoreOf seedMap)
        | n <= ssExactSplitLimit s = exhaustiveSearchWith scoreOf seedMap eps
        | otherwise                = let (pm, sc, _) = prunedBeamSearch cfg allWiresMovable scoreOf seedMap
                                     in (pm, sc)

      (ids0, ids1) = splitOfPartMap qIndexMap bestMap
      (distributedCirc, totalEbits) = synthesizeUnderQubitSplit circ ids0 ids1
      scoreName = "Edmonds phase + exact ULDU ranks (no synthesis in search)"

  reportDist $ "Qubit assignment: " ++ searchModeLabel s n ++ " from " ++ seedLabel s
  reportQpus ids0 ids1
  when (ssShowSteps s) $ reportSynthesisSteps circ ids0 ids1
  reportDist $ "Search score (" ++ scoreName ++ "): " ++ show searchScore
  when (ssValidateScore s) $
    reportDist $ "Algebraic score validation: " ++
                 (if searchScore == totalEbits then "PASS" else "MISMATCH")
  reportDist $ "Ebit cost: " ++ show totalEbits
  reportDistribution (verifyDist distributedCirc (partitionsOf ids0 ids1))
  return distributedCirc

{- Strategy 2: algebraic score with persistence tie-break, finalists fused -}
runPersistenceTieBreakSearch :: SplitSearchSettings -> SplitProblem -> IO [Primitive]
runPersistenceTieBreakSearch s sp = do
  let circ      = spCirc sp
      qIndexMap = spQIndex sp
      seedMap   = spSeed sp
      n         = length (spQubits sp)
      eps       = ssEpsilon s
      useBeam   = ssUseBeamSearch s
      exact     = n <= ssExactSplitLimit s

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

      -- The ORIGINAL (12-ebit benchmark) ranking, unchanged.
      (baselineMap, baselineScore)
        | not useBeam = (seedMap, rawScoreOf seedMap)
        | exact       = exhaustiveQubitSplitAlgebraic circ qIndexMap seedMap eps
        | otherwise   = beamSearchQubitSplitAlgebraic circ qIndexMap seedMap
                                                      eps (ssBeamWidth s) (ssDepth s)

      -- Persistence predicts only tie order. Raw algebraic cost is ALWAYS
      -- the first element of the ordering pair (raw, -predictedSaving).
      (tieMap, tieScore)
        | not useBeam = (seedMap, tieScoreOf seedMap)
        | exact       = exhaustiveQubitSplitPersistenceTieBreak circ qIndexMap seedMap eps
        | otherwise   = beamSearchQubitSplitPersistenceTieBreak circ qIndexMap seedMap
                                                                eps (ssBeamWidth s) (ssDepth s)

      -- Preserve the baseline in case the tie-aware beam follows a worse
      -- route. When both searches choose the same map, synthesize once.
      finalists
        | not (ssCompareRawBaseline s) || baselineMap == tieMap =
            [("persistence tie-break", tieMap)]
        | otherwise =
            [("raw-algebraic baseline", baselineMap),
             ("persistence tie-break", tieMap)]

      evaluateFinalist (origin, pm) =
        let (fIds0, fIds1) = splitOfPartMap qIndexMap pm
            (rawPredicted, reusePredicted, _) =
              persistenceScoreBreakdown ids summaries bounds invalidations fIds0
            -- Finalists only: this is NEVER called by a beam score.
            (rawCirc, rawEbits) = synthesizeUnderQubitSplit circ fIds0 fIds1
            (optCirc, saved)    = fusePersistentCats rawCirc
            total               = max 0 (rawEbits - saved)
        in EvaluatedSplit
             { evaluatedSource    = origin
             , evaluatedMap       = pm
             , evaluatedCircuit   = optCirc
             , evaluatedRawEbits  = rawEbits
             , evaluatedSaved     = saved
             , evaluatedEbits     = total
             , evaluatedAlgebraic = rawPredicted
             , evaluatedPredicted = reusePredicted
             , evaluatedValid     = verifyDist optCirc (partitionsOf fIds0 fIds1)
             }

      evaluated    = map evaluateFinalist finalists
      winner       = foldl1 betterFinalist evaluated
      (ids0, ids1) = splitOfPartMap qIndexMap (evaluatedMap winner)

  reportDist $ "Qubit assignment: " ++ searchModeLabel s n ++ " from " ++ seedLabel s
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
    when (ssValidateScore s) $
      reportDist $ "    Algebraic-vs-raw-synthesis: " ++
        (if evaluatedAlgebraic e == evaluatedRawEbits e
         then "PASS" else "MISMATCH")) evaluated

  reportDist $ "Selected finalist: " ++ evaluatedSource winner
  reportQpus ids0 ids1
  when (ssShowSteps s) $ reportSynthesisSteps circ ids0 ids1
  reportDist $ "Raw algebraic cost: " ++ show (evaluatedAlgebraic winner)
  reportDist $ "Predicted persistence saving (tie-break only): " ++
               show (evaluatedPredicted winner)
  reportDist $ "Actual fusion saving: " ++ show (evaluatedSaved winner)
  reportDist $ "Ebit cost: " ++ show (evaluatedEbits winner)
  reportDistribution (evaluatedValid winner)
  return (evaluatedCircuit winner)

{- Strategy 3: synthesize + cat-fuse every candidate -}
runFusedSearch :: SplitSearchSettings -> SplitProblem -> IO [Primitive]
runFusedSearch s sp = do
  let circ      = spCirc sp
      qIndexMap = spQIndex sp
      seedMap   = spSeed sp
      n         = length (spQubits sp)
      eps       = ssEpsilon s

      -- Search: every candidate is synthesized and cat-fused.
      (bestMap, searchScore, statsLine)
        | not (ssUseBeamSearch s) =
            (seedMap, fusedSplitScore circ qIndexMap seedMap, "no search")
        | n <= ssExactSplitLimit s =
            let (pm, sc) = exhaustiveQubitSplitFused circ qIndexMap seedMap eps
                count    = length (allBalancedWirePartitions eps seedMap)
            in (pm, sc, "exhaustive, " ++ show count ++ " splits synthesized")
        | otherwise =
            let (pm, sc, st) = beamSearchQubitSplitFused circ qIndexMap seedMap
                                 eps (ssBeamWidth s) (ssDepth s) (ssPatience s)
            in (pm, sc, "beam, " ++ show (statRounds st) ++ " rounds, "
                        ++ show (statEvaluations st) ++ " splits synthesized, stopped: "
                        ++ statStopReason st)

      -- Final synthesis of the chosen split.
      (ids0, ids1)        = splitOfPartMap qIndexMap bestMap
      (rawCirc, rawEbits) = synthesizeUnderQubitSplit circ ids0 ids1
      (optCirc, saved)    = fusePersistentCats rawCirc
      totalEbits          = max 0 (rawEbits - saved)

  reportDist $ "Qubit assignment: " ++ statsLine ++ ", from " ++ seedLabel s
  reportDist $ "Search objective: synthesize + cat fusion (ebits after fusion, raw ebits)"
  reportQpus ids0 ids1
  when (ssShowSteps s) $ reportSynthesisSteps circ ids0 ids1
  reportDist $ "Search score: " ++ show searchScore
  when (ssValidateScore s) $
    reportDist $ "Search-score-vs-synthesis: " ++
      (if searchScore == (totalEbits, rawEbits) then "PASS" else "MISMATCH")
  reportDist $ "Raw ebits (before fusion): " ++ show rawEbits
  reportDist $ "Fusion saving: " ++ show saved
  reportDist $ "Ebit cost: " ++ show totalEbits
  reportDistribution (verifyDist optCirc (partitionsOf ids0 ids1))
  return optCirc

buildDistributedCircuitWith :: SplitStrategy -> SplitSearchSettings
                            -> Int -> [ID] -> [Primitive] -> IO [Primitive]
buildDistributedCircuitWith strategy settings numParts qubits circ
  | numParts /= 2 = ioError . userError $
      "buildDistributedCircuit: supports exactly 2 QPUs, got " ++ show numParts
  | otherwise = do
      sp <- mkSplitProblem settings qubits circ
      reportDist $ "Split strategy: " ++ show strategy
      case strategy of
        AlgebraicSearch           -> runAlgebraicSearch           settings sp
        PersistenceTieBreakSearch -> runPersistenceTieBreakSearch settings sp
        FusedSearch               -> runFusedSearch               settings sp

buildDistributedCircuit :: Int -> [ID] -> [Primitive] -> IO [Primitive]
buildDistributedCircuit numParts qubits circ =
  buildDistributedCircuitWith strategy settings numParts qubits circ
  where
    strategy = PersistenceTieBreakSearch
    settings = defaultSplitSearchSettings
                 { ssValidateScore = False
                 , ssShowSteps     = False
                 , ssCompareRawBaseline = True
                 }