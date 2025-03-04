module Feynman.Optimization.Classical where

import Data.Map (Map, (!))
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Feynman.Core
import Feynman.Graph
import Feynman.Synthesis.Pathsum.Util

-- Basic process:
-- 1. unravel the circuit graph to get just the parts we can process
-- 2. compute irreversible output functions for all outputs
-- 3. synthesize/optimize the output functions into an irreversible graph
-- 4. optimize pebbling of the synthesized output back into a circuit
-- 5. reknit the final circuit using the saved stitches

-- You may wonder why we explicitly keep track of inoutIDs. After all, a sane
-- circuit shouldn't just output entangled garbage! Well, we are in the
-- business of exact synthesis here, but not with respect to ancilla use. I
-- would like for this function to be roughly idempotent, which means if it's
-- adding NEW ancilla inouts sometimes, it must have a way of forgetting the
-- OLD ones. Moreover, I don't want to waste time synthesizing ancilla
-- functions that in the best case are just fancy ways of computing nothing.

-- We cannot in general perfectly analyze the function that computes an
-- output, but even if we could, there's actually no clear distinction at a
-- circuit level between an ancilla which is returned to its original |0>
-- state, and a circuit that for practical reasons doesn't modify some of its
-- inputs, as in most adder designs.

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
      (classical, stitches, inoutRemap, unravelFreshIDs) =
        unravel isMCT freshIDs graph
      isMCT (MCT _ _) = True
      isMCT _ = False
      -- The unraveling will add a bunch of inputs and outputs, and we need to
      -- consider all the added ones as important, as well as the specifically
      -- identified ones passed in, which have new names now. Oof.
      unimportantOuts =
        foldReferences (flip Set.insert) Set.empty graph
          Set.\\ (Set.fromList inputIDs `Set.union` finCareOutIDs)
      importantOuts =
        foldReferences (flip Set.insert) Set.empty classical
          Set.\\ unimportantOuts
      -- Set.fromList inputIDs
      --   `Set.union` Set.fromList (map (Map.fromList inoutRemap !) inputIDs)
      --   `Set.union` Set.fromList (map (Map.fromList inoutRemap !) finCareOutIDs)

      -- compute XAG from remaining MCT circuit
      -- 2. compute irreversible output functions for all outputs
      

      -- collect subgraph of not-unimportant outputs
      -- 3. synthesize/optimize the output functions into an irreversible graph
      -- do minmultsat optimization
      -- 4. optimize pebbling of the synthesized output back into a circuit
      -- convert minmultsat back into an MCT circuit
      -- 5. reknit the final circuit using the saved stitches
      finGraph = graph
      finCareOutIDs = undefined
      finOutMap = undefined
      finFreshIDs = unravelFreshIDs
   in (finGraph, inputIDs, finCareOutIDs, finOutMap, finFreshIDs)
