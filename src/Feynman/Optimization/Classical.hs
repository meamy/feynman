module Feynman.Optimization.Classical where

import Data.Set (Set)
import Data.Set qualified as Set
import Feynman.Core
import Feynman.Graph

data ClassicalEquivalence q c = ClassicalEquivalence
  { gateHasLogicImplementation :: GraphGate q -> Bool,
    circuitToLogic :: q -> [GateQubit (GraphGate q)] -> c,
    logicToCircuit :: c -> (q, [GateQubit (GraphGate q)])
  }

resynthesizeClassical ::
  (HasFeynmanControl, CircuitGraph g, CircuitGate (GraphGate g), Show g, Show (GraphGate g), Show (GateQubit (GraphGate g))) =>
  g ->
  [GateQubit (GraphGate g)] ->
  ClassicalEquivalence g l ->
  [GateQubit (GraphGate g)] ->
  (g, [GateQubit (GraphGate g)])
resynthesizeClassical graph inoutIDs equiv freshIDs =
  (graph, inoutIDs)
  where
    -- repebbleAncillas (pebblingStrategy)
    (classical, nonClassical, remainFreshIDs) =
      unravel (gateHasLogicImplementation equiv) freshIDs graph
