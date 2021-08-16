module Feynman.Optimization.TPar where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Matroid
import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible
import Feynman.Synthesis.Reversible.Parallel
import Feynman.Synthesis.Reversible.Gray
import Feynman.Optimization.Swaps

import Data.List hiding (transpose)
import Data.Ord (comparing)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Bits

{- Generalized T-par -}
{- Soundly (by abstracting Hadamards and other
 - uninterpreted gates) separate circuits into
 - CNOT-dihedral chunks with fixed (must) and
 - floating (may) phases. We do this by
 - performing forward and backward analysis,
 - followed by synthesis of the CNOT-dihedral
 - chunks -}
       
{- TODO: Merge with phase folding eventually -}

type PhasePoly = Map F2Vec Angle

data AnalysisState = SOP {
  dim     :: Int,
  ivals   :: AffineTrans,
  qvals   :: AffineTrans,
  terms   :: PhasePoly,
  phase   :: Angle
} deriving Show

type Analysis = State AnalysisState

data Chunk =
    CNOTDihedral AffineTrans AffineTrans PhasePoly PhasePoly
  | UninterpGate Primitive
  | GlobalPhase  ID Angle
  deriving Show

{- Get the bitvector for variable v -}
getSt :: ID -> Analysis (F2Vec, Bool)
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> error $ "No qubit \"" ++ v ++ "\" found in t-par"

{- existentially quantifies a variable then
 - orphans all terms that are no longer in the linear span of the
 - remaining variable states and assigns the quantified variable
 - a fresh (linearly independent) state -}
exists :: ID -> AnalysisState -> Analysis (PhasePoly, PhasePoly)
exists v st@(SOP dim ivals qvals terms phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v qvals
      (vecs, cnsts) = unzip avecs
      (may, must)   = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = zip vecs' $ cnsts ++ [False]
      ivals'        = Map.fromList $ zip (vars ++ [v]) avecs'
      terms'        = if dim' > dim
                      then Map.mapKeysMonotonic (zeroExtend 1) may
                      else may
  in do
    put $ SOP dim' ivals' ivals' terms' phase
    return (must, may)

replaceIval :: AffineTrans -> AnalysisState -> AnalysisState
replaceIval ivals' st = st { ivals = ivals' }

updateQval :: ID -> (F2Vec, Bool) -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

addTerm :: (F2Vec, Bool) -> Angle -> AnalysisState -> AnalysisState
addTerm (bv, p) i st =
  case p of
    False -> st { terms = Map.alter (f i) bv $ terms st }
    True ->
      let terms' = Map.alter (f (-i)) bv $ terms st
          phase' = phase st + i
      in
        st { terms = terms', phase = phase' }
  where f i oldt = case oldt of
          Just x  -> Just $ x + i
          Nothing -> Just $ i

{-- The main analysis -}
applyGate :: [Chunk] -> Primitive -> Analysis [Chunk]
applyGate acc g = case g of
  T v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 2)
    return acc
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 7 2)
    return acc
  S v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 1)
    return acc
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 3 1)
    return acc
  Z v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 0)
    return acc
  Rz p v -> do
    bv <- getSt v
    modify $ addTerm bv p
    return acc
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
    return acc
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
    return acc
  CZ c t -> do            -- Expanding it out to CNOT and S
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ addTerm (bvc, bc) (dyadicPhase $ dyadic 1 1)
    modify $ addTerm (bvt, bt) (dyadicPhase $ dyadic 1 1)
    modify $ addTerm (bvc + bvt, bc `xor` bt) (dyadicPhase $ dyadic 3 1)
    return acc
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
    return acc
  _        -> do
    let args = getArgs g
    _   <- mapM getSt args
    st  <- get
    (musts, mays) <- liftM unzip $ mapM (\v -> get >>= exists v) args
    let (must, may) = (Map.unionsWith (+) musts, Map.unionsWith (+) mays)
    return $ (UninterpGate g):(CNOTDihedral (ivals st) (qvals st) must may):acc

chunkify :: [ID] -> [ID] -> [Primitive] -> [Chunk]
chunkify vars inputs gates =
  let (chunks, st) = runState (foldM applyGate [] gates) init
      final        = CNOTDihedral (ivals st) (qvals st) (terms st) Map.empty
      global       = GlobalPhase (head vars) (phase st)
  in
      global:final:chunks
  where n        = length vars
        vals     = Map.fromList . map f $ zip vars [0..]
        f (v, i) = (v, if v `elem` inputs then (bitI n i, False) else (bitVec n 0, False))
        init     = SOP n vals vals Map.empty 0

-- Propagates phases backwards as far as possible
backPropagate :: [Chunk] -> [Chunk]
backPropagate chunks = evalState (foldM processChunk [] chunks) (Map.empty, Map.empty)
  where processChunk acc chunk = case chunk of
          CNOTDihedral i o must may -> do
            (st, phases)  <- get
            let n    = width.fst.head.Map.elems $ i
            let may' = Map.union (Map.mapKeys (flip (@@) (n-1,0)) phases) may
            put (i, Map.union must may')
            return $ (CNOTDihedral i o must may'):acc
          UninterpGate g -> do
            (st, phases) <- get
            let vecs  = fst.unzip.snd.unzip.Map.toList.foldr Map.delete st $ getArgs g
            let float = Map.filterWithKey (\b _ -> inLinearSpan vecs b) phases
            put (st, float)
            return $ chunk:acc
          GlobalPhase v angle -> return $ chunk:acc

synthesizeChunks :: AffineSynthesizer -> [Chunk] -> [Primitive]
synthesizeChunks synth chunks = evalState (foldM synthesizeChunk [] chunks) Map.empty
  where synthesizeChunk acc chunk = case chunk of
          CNOTDihedral i o must may -> do
            applied <- get
            let must'        = Map.differenceWith subtract must applied
            let may'         = Map.differenceWith subtract may applied
            let applied'     = Map.difference applied must
            let (gates, rem) = synth i o (Map.toList must') (Map.toList may')
            put $ Map.unionWith (+) applied' (Map.difference may' $ Map.fromList rem)
            return $ acc ++ gates
          UninterpGate g            -> return $ acc ++ [g]
          GlobalPhase v angle       -> return $ acc ++ globalPhase v angle
        subtract a b = if a == b then Nothing else Just $ a - b

gtpar :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtpar synth vars inputs gates = synthesizeChunks (affineTrans synth) chunks
  where chunks = backPropagate $ chunkify vars inputs gates

gtparFast :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtparFast synth vars inputs gates = synthesizeChunks (affineTrans synth') chunks
  where chunks = chunkify vars inputs gates
        synth' = \i o mu ma -> (fst $ synth i o mu [], ma)

{- Optimization algorithms -}

-- t-par: the t-par algorithm from [AMM2014]
tpar i o = pushSwaps . gtpar tparMaster i o

-- minCNOT: the CNOT minimization algorithm from [AAM17]
minCNOT = gtpar cnotMinGrayPointed

{- Open synthesis -}
applyGateOpen :: AffineOpenSynthesizer -> [Primitive] -> Primitive -> Analysis [Primitive]
applyGateOpen synth gates g = case g of
  T v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 2)
    return gates
  Tinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 7 2)
    return gates
  S v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 1)
    return gates
  Sinv v   -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 3 1)
    return gates
  Z v      -> do
    bv <- getSt v
    modify $ addTerm bv (dyadicPhase $ dyadic 1 0)
    return gates
  Rz p v -> do
    bv <- getSt v
    modify $ addTerm bv p
    return gates
  X v      -> do
    (bv, b) <- getSt v
    modify $ updateQval v (bv, Prelude.not b)
    return gates
  CNOT c t -> do
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ updateQval t (bvc + bvt, bc `xor` bt)
    return gates
  CZ c t -> do            -- Expanding it out to CNOT and S
    (bvc, bc) <- getSt c
    (bvt, bt) <- getSt t
    modify $ addTerm (bvc, bc) (dyadicPhase $ dyadic 1 1)
    modify $ addTerm (bvt, bt) (dyadicPhase $ dyadic 1 1)
    modify $ addTerm (bvc + bvt, bc `xor` bt) (dyadicPhase $ dyadic 3 1)
    return gates
  Swap u v -> do
    bvu <- getSt u
    bvv <- getSt v
    modify $ updateQval u bvv
    modify $ updateQval v bvu
    return gates
  _        -> do
    let args = getArgs g
    _   <- mapM getSt args
    st  <- get
    (musts, mays) <- liftM unzip $ mapM (\v -> get >>= exists v) args
    let (must, may) = (Map.unionsWith (+) musts, Map.unionsWith (+) mays)
    let (out, parities)    = synth (ivals st) (Map.toList must)
        (out', correction) =
          let f (i, g) v = (\(i', g') -> (i', g++g')) (unifyAffine v i (qvals st)) in
            foldl' f (out, []) args
    st' <- get
    let out'' = if (dim st') > (dim st) then Map.map (\(bv, b) -> (zeroExtend 1 bv, b)) out' else out'
    modify $ replaceIval $ foldr (\v -> Map.insert v ((qvals st')!v)) out'' args
    return $ gates ++ parities ++ correction ++ [g]

finalizeOpen :: AffineOpenSynthesizer -> [Primitive] -> Analysis [Primitive]
finalizeOpen synth gates = do
  st <- get
  let (out', parities) = synth (ivals st) (Map.toList $ terms st)
  let asynth           = affineTrans (\i o _ may -> (linearSynth i o, may))
  let (circ, [])       = asynth out' (qvals st) [] []
  return $ gates ++ parities ++ circ
                 ++ (globalPhase (head . Map.keys . ivals $ st) $ phase st)
    
gtparopen :: OpenSynthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtparopen osynth vars inputs gates =
  let synth = affineTransOpen osynth
      init = 
        SOP { dim = dim', 
              ivals = Map.fromList ivals, 
              qvals = Map.fromList ivals, 
              terms = Map.empty,
              phase = 0 }
  in
    evalState (foldM (applyGateOpen synth) [] gates >>= finalizeOpen synth) init
  where dim'    = length inputs
        bitvecs = [(bitI dim' x, False) | x <- [0..]] 
        ivals   = zip (inputs ++ (vars \\ inputs)) bitvecs


{- Open-ended optimizers -}

-- Gray-synth with open ends
minCNOTOpen = gtparopen cnotMinGrayOpen

-- Compares between open and closed CNOT minimization. Slowest configuration
minCNOTMaster vars inputs gates =
  let option1 = gtpar cnotMinGrayPointed vars inputs gates
      option2 = gtparopen cnotMinGrayOpen vars inputs gates
      isct g = case g of
        CNOT _ _  -> True
        otherwise -> False
      countc = length . filter isct
  in
    minimumBy (comparing countc) [option1, option2]
