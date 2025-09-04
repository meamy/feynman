{-|
Module      : TPar
Description : CNOT-Dihedral re-synthesis algorithms
Copyright   : (c) 2016-2025 Matthew Amy
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

This module implements the T-par algorithm from
  [arxiv:1303.2042](https://arxiv.org/abs/1303.2042).
The T-parallelizing synthesis of CNOT-dihedral chunks,
corresponding to circuits over the gates

  @CNOT, X, RZ(theta)@

can be replaced with other CNOT-dihedral synthesis
methods, such as [GraySynth](https://arxiv.org/abs/1712.01859).

The T-par algorithm operates by computing the sum-over-paths representation
of the circuit

  @|x1 x2 ... xn> --> sum[y1, ..., yk] e^{i f(x, y)} |A(x, y) + b>@

where `f` is expressed in the parity basis. The sum-over-paths representation
is broken into CNOT-dihedral chunks of the form

  @|A(x, y) + b> --> e^{i f(x, y)} |A'(x, y) + b'>@

which are then fed into a supplied CNOT-dihedral synthesizer. Note that the input,
as well as the output of a CNOT-dihedral chunk is given as a basis of an affine
subspace of \(\mathbb{Z}_2^{n+k}\) --- this is done to better reflect the logical structure
of the circuit and to allow the affine synthesizer to make use of ancillas already initialized
to parities of other bits. Likewise, phases which may commute to the next chunk are identified
and passed to the synthesizer to retain flexibility in the placement of phase terms.

-}

module Feynman.Optimization.TPar where

import Data.List hiding (transpose)
import Data.Ord (comparing)

import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Lazy

import Data.Bits

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Algebra.Matroid
import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible
import Feynman.Synthesis.Reversible.Parallel
import Feynman.Synthesis.Reversible.Gray

-- * Optimization interface
------------------------------------

-- | T-par algorithm, parameterized by a CNOT-dihedral synthesis algorithm
gtpar :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtpar synth vars inputs gates = synthesizeChunks (affineTrans synth) chunks
  where chunks = backPropagate $ chunkify vars inputs gates

-- | A faster version which does not backpropagate phase terms
gtparFast :: Synthesizer -> [ID] -> [ID] -> [Primitive] -> [Primitive]
gtparFast synth vars inputs gates = synthesizeChunks (affineTrans synth') chunks
  where chunks = chunkify vars inputs gates
        synth' = \i o mu ma -> (fst $ synth i o mu [], ma)

-- * Specific instances
------------------------------------

-- | The T-par algorithm of [AMM13](https://arxiv.org/abs/1303.2042).
--   Optimizes for T-depth by synthesizing T-depth optimal CNOT-dihedral subcircuits
--   using Matroid partitioning
tpar :: [ID] -> [ID] -> [Primitive] -> [Primitive]
tpar i o = pushSwaps . gtpar tparMaster i o

-- | The CNOT optimization algorithm of [AAM17](https://arxiv.org/abs/1712.01859).
--   Uses GraySynth to perform CNOT-dihedral synthesis
minCNOT :: [ID] -> [ID] -> [Primitive] -> [Primitive]
minCNOT = gtpar cnotMinGrayPointed

-- | Gray-synth with open ends
minCNOTOpen :: [ID] -> [ID] -> [Primitive] -> [Primitive]
minCNOTOpen = gtparopen cnotMinGrayOpen

-- | Compares between open and closed CNOT minimization and takes the best result
minCNOTMaster :: [ID] -> [ID] -> [Primitive] -> [Primitive]
minCNOTMaster vars inputs gates =
  let option1 = gtpar cnotMinGrayPointed vars inputs gates
      option2 = gtparopen cnotMinGrayOpen vars inputs gates
      isct g = case g of
        CNOT _ _  -> True
        otherwise -> False
      countc = length . filter isct
  in
    minimumBy (comparing countc) [option1, option2]

-- * Algorithm internals
------------------------------------

-- | A Phase polynomial here is an association of angles to (affine) parities
type PhasePoly = Map F2Vec Angle

-- | Representation of subcircuit chunks in the T-par algorithm.
--   Subcircuits are either global phase, a non-CNOT-dihedral gate, or a
--   a CNOT-dihedral chunk which consist of
--
--     1. A set of (affine) vectors giving the input state
--     2. A set of (affine) vectors giving the output state
--     3. Phase terms which *must* be applied in this chunk -- i.e. do not commute right
--     4. Phase terms which *may* be applied in this chunk -- i.e. commute right
--
--   Notably, `CNOTDihedral input output must may` represents the CNOT-dihedral operator
--
--     @ |input> --> e^i{must + may}|output> @
--
--   where the *must* phases do not commute beyond the subcircuit boundary on the right,
--   and the *may* phases do commute beyond the boundary
data Chunk =
    CNOTDihedral AffineTrans AffineTrans PhasePoly PhasePoly
  | UninterpGate Primitive
  | GlobalPhase ID Angle
  deriving Show

-- | Phase polynomial representation of the current state
data AnalysisState = SOP {
  dim     :: Int,          -- ^ Number of variables
  ivals   :: AffineTrans,  -- ^ Initial state
  qvals   :: AffineTrans,  -- ^ Final state
  terms   :: PhasePoly,    -- ^ Phase polynomial terms
  phase   :: Angle         -- ^ Global phase
} deriving Show

-- | Convenience type for threading the state through the analysis
type Analysis = State AnalysisState


-- | Get the state of a variable in the analysis
getSt :: ID -> Analysis (F2Vec, Bool)
getSt v = do 
  st <- get
  case Map.lookup v (qvals st) of
    Just bv -> return bv
    Nothing -> error $ "No qubit \"" ++ v ++ "\" found in t-par"

-- | Existentially quantifies a variable by orphaning all terms which are no longer
--   in the linear span of the ket
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

-- | Replaces the initial state of the analysis
replaceIval :: AffineTrans -> AnalysisState -> AnalysisState
replaceIval ivals' st = st { ivals = ivals' }

-- | Updates the final state of some qubit to an affine sum of variables
updateQval :: ID -> (F2Vec, Bool) -> AnalysisState -> AnalysisState
updateQval v bv st = st { qvals = Map.insert v bv $ qvals st }

-- | Adds a term to the phase polynomial
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

-- | State transformer for individual gates. Takes the current
--   list of chunks as an argument
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

-- | The chunking algorithm. Performs the phase polynomial analysis, accumulating
--   CNOT-dihedral chunks as it goes
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

-- | Post processing step. Runs an abridged version of the analysis in reverse to
--   determine the left boundary of phase terms (i.e. how far left in the circuit they commute)
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

-- | Synthesis step. Invokes an "AffineSynthesizer" on the CNOT-dihedral chunks
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

{-----------------------------------
 Open synthesis
 -----------------------------------}

-- * Open synthesis
--
-- $ These methods use open CNOT-dihedral synthesizers, which synthesize
--   CNOT-dihedral circuits up to some affine computational basis
--   permutation. The added flexibility allows more optimization in some cases
--   via sharing between CNOT-dihedral chunks

-- | Gate transformers for open-ended synthesis
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

-- | Performs a final synthesis to compute `|A(x,y) + b>`
finalizeOpen :: AffineOpenSynthesizer -> [Primitive] -> Analysis [Primitive]
finalizeOpen synth gates = do
  st <- get
  let (out', parities) = synth (ivals st) (Map.toList $ terms st)
  let asynth           = affineTrans (\i o _ may -> (linearSynth i o, may))
  let (circ, [])       = asynth out' (qvals st) [] []
  return $ gates ++ parities ++ circ
                 ++ (globalPhase (head . Map.keys . ivals $ st) $ phase st)
    
-- | The open-ended T-par algorithm
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


