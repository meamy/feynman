module Feynman.Optimization.Swaps (pushSwaps) where

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Feynman.Core

-- | Push swaps to the end
pushSwaps :: [Primitive] -> [Primitive]
pushSwaps = reverse . go (Map.empty, []) where

  get :: Map ID ID -> ID -> ID
  get ctx q               = Map.findWithDefault q q ctx

  -- Beware, the final synthesis of swaps is a bit subtle. The ctx map
  -- expresses a permutation, and we decompose it into a series of orbits aka
  -- cycles. When emitting the swap gates for each orbit, the order of the
  -- swaps is important, because it determines which way around the orbit the
  -- elements are cycling. If you reverse the order of two swaps, those
  -- elements will cycle in the opposite direction from the others, and you
  -- won't get the orbit you wanted.
  synthesize :: (Map ID ID, [Primitive]) -> [Primitive]
  synthesize (ctx, acc) =
    case Map.toList ctx of
      [] -> acc
      (q, q'):_ -> synthesize (synthesizeOrbit q' (Map.delete q ctx, acc))

  -- Since we're deleting elements as we go, failure to find the next element
  -- in the chain indicates we've come back to the start and are done.
  synthesizeOrbit :: ID -> (Map ID ID, [Primitive]) -> (Map ID ID, [Primitive])
  synthesizeOrbit q (ctx, acc) =
      case ctx Map.!? q of
        Just q' -> synthesizeOrbit q' (Map.delete q ctx, (Swap q q'):acc)
        Nothing -> (ctx, acc)

  -- This algorithm operates in two phases: first it walks through the list of
  -- gates, building up a mapping as it goes (which is really just the overall
  -- permutation the sequence of swaps represents). At the same time it removes
  -- any Swap (using the args to update the mapping), and rewrites the qubit
  -- references in the circuit. That leaves you with an equivalent circuit,
  -- modulo swaps. The second phase is implemented by "synthesize" above: it
  -- emits a sequence of swaps to make the equivalence exact.
  go :: (Map ID ID, [Primitive]) -> [Primitive] -> [Primitive]
  go (ctx, acc) []        = synthesize (ctx, acc)
  go (ctx, acc) (x:xs)    = case x of
    Swap q1 q2 ->
      let (q1', q2') = (get ctx q1, get ctx q2) in
        go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs
    gate       -> go (ctx, substGate (get ctx) gate:acc) xs
