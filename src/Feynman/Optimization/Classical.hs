module Feynman.Optimization.Classical where

import Data.Map (Map, (!))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Feynman.Core
import Feynman.Graph
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.Util (fromMCTs)

-- Basic outline of the process:
-- 1. unravel the circuit graph to get just the parts we can process
-- 2. compute irreversible output functions for all outputs
-- 3. synthesize/optimize the output functions into an irreversible graph
-- 4. optimize pebbling of the synthesized output back into a circuit
-- 5. reknit the final circuit using the saved stitches

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

resynthesizeClassical :: (HasFeynmanControl) => [ExtractionGates] -> [ID] -> [ID] -> [ID] -> ([ExtractionGates], [ID], [ID], [(ID, ID)], [ID])
resynthesizeClassical graph inputIDs careOutIDs freshIDs =
  let -- 1. unravel the circuit graph to get just the parts we can process
      (mcts, stitches, inoutRemap, unravelFreshIDs) =
        unravel isMCT freshIDs graph
      isMCT (MCT _ _) = True
      isMCT _ = False
      -- The unraveling will add a bunch of inputs and outputs, and we need to
      -- consider all the added ones as important, as well as the specifically
      -- identified ones passed in, which have new names now. So, we figure
      -- out which of the originals were specifically UNimportant, and exclude
      -- those.
      unimportantOuts =
        foldReferences (flip Set.insert) Set.empty graph
          Set.\\ (Set.fromList inputIDs `Set.union` finCareOutIDs)
      importantOuts =
        foldReferences (flip Set.insert) Set.empty mcts
          Set.\\ unimportantOuts
      -- Set.fromList inputIDs
      --   `Set.union` Set.fromList (map (Map.fromList inoutRemap !) inputIDs)
      --   `Set.union` Set.fromList (map (Map.fromList inoutRemap !) finCareOutIDs)

      -- 2. compute irreversible output functions for all outputs
      (initialXAG, initialInOrder, initialOutOrder) = fromMCTs mcts

      -- 3. synthesize/optimize the output functions into an irreversible graph
      -- do minmultsat optimization

      -- 4. optimize pebbling of the synthesized output back into a circuit
      -- convert minmultsat back into an MCT circuit

      -- 5. reknit the final circuit using the saved stitches

      finGraph = reknit mcts stitches
      finCareOutIDs = undefined
      finOutMap = undefined
      finFreshIDs = unravelFreshIDs
   in (finGraph, inputIDs, finCareOutIDs, finOutMap, finFreshIDs)
