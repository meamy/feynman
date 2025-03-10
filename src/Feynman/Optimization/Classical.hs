module Feynman.Optimization.Classical where

import Control.Monad.State.Strict
import Data.Bifunctor (bimap, second)
import Data.Foldable (foldl')
import Data.Map (Map, (!))
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace (trace)
import Feynman.Core
import Feynman.Graph
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.Reversible.Allocation
import Feynman.Synthesis.Reversible.Allocation.ComputeFirst (computeFirstAllocate)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.MinMultSat (resynthesizeMinMultSat)
import Feynman.Synthesis.XAG.Util (fromMCTs, toMCTs)

-- Basic outline of the process:
-- 1. expand controlled phase controls into classical logic
-- 2. unravel the circuit graph to get just the parts we can process
-- 3. compute irreversible output functions for all outputs
-- 4. synthesize/optimize the output functions into an irreversible graph
-- 5. translate the resynthesized XAG back into a circuit
-- 6. reknit the final circuit using the saved stitches
-- 7. optimize the qubit use in the resulting circuit

-- You may wonder why we explicitly keep track of inputIDs and careOutIDs. The
-- implication is there are outputs we don't care about, and a circuit should
-- be fully specified, otherwise you're outputting entangled garbage you can't
-- uncompute, and it shouldn't ask for any more ancillas than it's using.

-- Well, if we're resynthesizing the circuit, the number of ancillas may
-- change, so it's important to know which inputs and outputs are ancillas in
-- the first place. We cannot in general perfectly analyze the function that
-- computes an output, but even if restrict ourselves to circuits we can fully
-- analyze, there's actually no clear distinction at a circuit level between
-- an ancilla which is returned to its original |0> state, and a circuit that
-- for practical reasons doesn't modify some of its inputs, as in most adder
-- designs.

-- So, we leave it to the user to specify which lines they care about.

-- Right now the interface takes (and returns) "inputIDs" and "careOutIDs",
-- which are respectively the inpupts which cannot be assumed initialized to
-- zero, and the outputs which will become primary outputs or be used later in
-- another portion of the circuit, if this is a subcircuit.

-- Ideally all remaining qubits used should be uncomputed to zero, but if the
-- algorithm is not able to find a solution under that constraint, as a
-- compromise it may leave one or more outputs in the input state and compute
-- the desired function into a fresh ancilla instead.

resynthesizeClassical ::
  (HasFeynmanControl) =>
  [ExtractionGates] ->
  [ID] ->
  [ID] ->
  [ID] ->
  ([ExtractionGates], [(ID, ID)], [(ID, ID)], [ID])
resynthesizeClassical circ inputIDs careOutIDs freshIDs =
  let -- The unraveling will add a bunch of inputs and outputs, and we need to
      -- consider all the added ones as important, as well as the specifically
      -- identified ones passed in, which have new names now. So, we figure
      -- out which of the originals were specifically UNimportant, and exclude
      -- those.
      unimportantOuts =
        foldReferences (flip Set.insert) Set.empty circ
          Set.\\ (Set.fromList inputIDs `Set.union` Set.fromList careOutIDs)
      importantOuts =
        foldReferences (flip Set.insert) Set.empty mcts
          Set.\\ unimportantOuts

      -- 1. expand controlled phase gates in the circuit graph to MCT into
      --    ancilla + uncontrolled phase
      (exPhaseGraph, exPhaseFreshIDs) = expandPhase freshIDs circ

      -- 2. unravel the circuit graph to get just the parts we can process
      (mcts, stitches, inoutRemap, unravelFreshIDs) =
        unravel isMCT exPhaseFreshIDs exPhaseGraph
      isMCT (MCT _ _) = True
      isMCT _ = False

      -- 3. compute irreversible output functions for all outputs
      -- Here we drop the unimportantOuts implicitly, all we really want from
      -- the MCTs is a specification of the Boolean functions for the
      -- importantOuts
      (initialXAG, initialInOrder, initialOutOrder) =
        fromMCTs mcts inputIDs careOutIDs

      -- 4. synthesize/optimize the output functions into an irreversible graph
      maybeResynthXAG = resynthesizeMinMultSat initialXAG
      resynthXAG = fromMaybe initialXAG maybeResynthXAG

      -- 5. translate the resynthesized XAG back into a circuit
      -- This will allocate plenty ancillas, but we deal with that after the
      -- reknitting
      (resynthMCTs, resynthFreshIDs) =
        toMCTs resynthXAG initialInOrder initialOutOrder unravelFreshIDs

      -- 6. reknit the circuit using the saved stitches
      reknitCirc = reknit resynthMCTs stitches

      -- 7. optimize the qubit use in the resulting circuit
      maybeFinRealloc = reallocateQubits reknitCirc inputIDs careOutIDs resynthFreshIDs
      (finCirc, finInputOutMap, finCareOutMap, finFreshIDs) =
        fromMaybe (error "Qubit final allocation failed") maybeFinRealloc
   in (finCirc, finInputOutMap, finCareOutMap, finFreshIDs)

-- for now, do nothing
expandPhase :: [ID] -> [ExtractionGates] -> ([ExtractionGates], [ID])
expandPhase freshIDs circ = (circ, freshIDs)

reallocateQubits ::
  [ExtractionGates] ->
  [ID] ->
  [ID] ->
  [ID] ->
  Maybe ([ExtractionGates], [(ID, ID)], [(ID, ID)], [ID])
reallocateQubits circ inIDs outIDs idSource =
  -- trace ("inputRes " ++ show inputRes) $
  -- trace ("initRes " ++ show (take 3 initRes)) $
  -- trace ("gtcsRemainCmpt " ++ show (take 3 (gtcsRemainCmpt gtcs))) $
  -- trace ("gtcsRemainRes " ++ show (take 3 (gtcsRemainRes gtcs))) $
  -- trace ("gtcsQubits " ++ show (gtcsQubits gtcs)) $
  -- trace ("gtcsPhaseRes " ++ show (gtcsPhaseRes gtcs)) $
  -- trace ("gtcsComputations " ++ show (gtcsComputations gtcs)) $
  -- trace ("phaseRes " ++ show (phaseRes)) $
  -- trace ("outRes " ++ show (outRes)) $
  -- trace ("computations " ++ show computations) $
  -- trace ("prob computations " ++ show (Feynman.Synthesis.Reversible.Allocation.computations prob)) $
  -- trace ("prob permittedResults " ++ show (permittedResults prob)) $
  -- trace ("prob requiredResults " ++ show (requiredResults prob)) $
  -- trace ("prob initialState " ++ show (initialState prob)) $
  allocation
    >>= \seq ->
      ( do
          let initCtx = Map.fromList (zip inputRes inIDs)
              gates = foldr processComputation [] seq
          return (gates, zip inIDs inIDs, undefined, idSource)
          -- finMCTs, finInIDs, finOutIDs, finIDSource
      )
  where
    processComputation = undefined
    allocation = computeFirstAllocate prob

    prob = problemFrom computations (outRes ++ phaseRes) inputRes inputRes
    computations =
      map
        (second (bimap resultsFromList resultsFromList))
        (gtcsComputations gtcs)
    outRes = map (gtcsQubits gtcs !) outIDs
    phaseRes = Set.toList (gtcsPhaseRes gtcs)

    (_, gtcs) =
      runState
        (mapM_ gateToComputation circ >>= addDups inputRes)
        ( defaultGTCState
            { gtcsRemainRes = initRes,
              gtcsQubits = Map.fromList (zip inIDs inputRes)
            }
        )
    (inputRes, initRes) = splitAt (length inIDs) freshResults

data GTCState = GTCState
  { gtcsRemainCmpt :: [Computation],
    gtcsRemainRes :: [ComputedResult],
    gtcsQubits :: Map ID ComputedResult,
    gtcsPhaseRes :: Set ComputedResult,
    gtcsComputations :: [(Computation, ([ComputedResult], [ComputedResult]))],
    gtcsCmptToGates :: [(Computation, [ID] -> ExtractionGates)]
  }

defaultGTCState :: GTCState
defaultGTCState =
  GTCState
    { gtcsRemainCmpt = freshComputations,
      gtcsRemainRes = freshResults,
      gtcsQubits = Map.empty,
      gtcsPhaseRes = Set.empty,
      gtcsComputations = [],
      gtcsCmptToGates = []
    }

addDups :: [ComputedResult] -> () -> State GTCState ()
addDups inputRes _ = do
  cmpts <- gets gtcsComputations
  phaseRes <- gets gtcsPhaseRes
  -- all
  let allRes =
        foldl'
          (\rs (_, (_, ys)) -> Set.union rs (Set.fromList ys))
          (Set.fromList inputRes)
          cmpts
      hasDup = Set.fromList . map (\(_, (_, y : ys)) -> y) . filter isDup $ cmpts
  mapM_ addDup (allRes Set.\\ hasDup Set.\\ phaseRes)
  where
    isDup (_, (ns, ys)) =
      let noAncN = filter (/= zeroAncilla) ns
       in (length noAncN == 1) && ys == noAncN ++ noAncN
    addDup rx =
      modify
        ( \st ->
            let (c : remainCmpt) = gtcsRemainCmpt st
             in st
                  { gtcsComputations = (c, ([rx, zeroAncilla], [rx, rx])) : gtcsComputations st,
                    gtcsCmptToGates = (c, \[x, a] -> MCT [x] a) : gtcsCmptToGates st,
                    gtcsRemainCmpt = remainCmpt
                  }
        )

gateToComputation :: ExtractionGates -> State GTCState ()
gateToComputation gate =
  case gate of
    Hadamard x -> do
      rx <- getQubit x
      r <- addComputation (\r -> (([rx], [r]), \[x] -> Hadamard x))
      setQubit x r
    Phase theta ys -> do
      rys <- mapM getQubit ys
      r <- addComputation (\r -> ((rys, r : rys), \(_ : ys) -> Phase theta ys))
      return ()
    MCT ys x -> do
      rx <- getQubit x
      rys <- mapM getQubit ys
      r <- addComputation (\r -> ((rx : rys, r : rys), \(x : ys) -> MCT ys x))
      setQubit x r
    Swapper x y -> return ()

setQubit :: ID -> ComputedResult -> State GTCState ()
setQubit x r = modify (\st -> st {gtcsQubits = Map.insert x r (gtcsQubits st)})

getQubit :: ID -> State GTCState ComputedResult
getQubit x = (! x) <$> gets gtcsQubits

addComputation :: (ComputedResult -> (([ComputedResult], [ComputedResult]), [ID] -> ExtractionGates)) -> State GTCState ComputedResult
addComputation f = do
  st <- get
  let (r : remainRes) = gtcsRemainRes st
      (c : remainCmpt) = gtcsRemainCmpt st
      (desc, toGates) = f r
  put
    st
      { gtcsRemainCmpt = remainCmpt,
        gtcsRemainRes = remainRes,
        gtcsComputations = (c, desc) : gtcsComputations st,
        gtcsCmptToGates = (c, toGates) : gtcsCmptToGates st
      }
  return r
