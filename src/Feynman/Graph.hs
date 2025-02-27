{-# LANGUAGE TypeFamilies #-}

module Feynman.Graph where

import Control.Monad.State.Strict (State (..), evalState, gets)
import Data.Foldable (Foldable (..), foldl')
import Data.Kind (Type)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (for)
import Feynman.Core

class (Ord (GateQubit g), Eq (GateQubit g)) => CircuitGate g where
  type GateQubit g :: Type
  foldGateReferences :: (a -> GateQubit g -> a) -> a -> g -> a
  mapGateReferences :: (GateQubit g -> GateQubit g) -> g -> g

class
  (CircuitGate (GraphGate g), Ord (GateQubit (GraphGate g)), Eq (GateQubit (GraphGate g))) =>
  CircuitGraph g
  where
  -- type GraphQubit g :: Type
  type GraphGate g :: Type
  foldGates :: (a -> GraphGate g -> a) -> a -> g -> a
  foldReferences :: (a -> GateQubit (GraphGate g) -> a) -> a -> g -> a
  mapGates :: (GraphGate g -> GraphGate g) -> g -> g
  mapReferences :: (GateQubit (GraphGate g) -> GateQubit (GraphGate g)) -> g -> g
  pureGates :: g
  appendGate :: g -> GraphGate g -> g

-- In a way, it's nice that Haskell lets me do this.
-- In another way, it would be nicer if Feynman didn't use 3 different gate
-- representations, and I didn't feel like I had to do this.
instance (CircuitGate g) => CircuitGraph [g] where
  type GraphGate [g] = g
  foldGates f = foldr (flip f)
  foldReferences f = foldr (flip (foldGateReferences f))
  mapGates = map
  mapReferences f = map (mapGateReferences f)
  pureGates = []
  appendGate graph g = g : graph

instance CircuitGate Primitive where
  type GateQubit Primitive = ID

  foldGateReferences f a (H xID) = f a xID
  foldGateReferences f a (X xID) = f a xID
  foldGateReferences f a (Y xID) = f a xID
  foldGateReferences f a (Z xID) = f a xID
  foldGateReferences f a (CNOT xID yID) = f (f a xID) yID
  foldGateReferences f a (CZ xID yID) = f (f a xID) yID
  foldGateReferences f a (S xID) = f a xID
  foldGateReferences f a (Sinv xID) = f a xID
  foldGateReferences f a (T xID) = f a xID
  foldGateReferences f a (Tinv xID) = f a xID
  foldGateReferences f a (Swap xID yID) = f (f a xID) yID
  foldGateReferences f a (Rz theta xID) = f a xID
  foldGateReferences f a (Rx theta xID) = f a xID
  foldGateReferences f a (Ry theta xID) = f a xID
  foldGateReferences f a (Measure xID yID) = f (f a xID) yID
  foldGateReferences f a (Reset xID) = f a xID
  foldGateReferences f a (Uninterp name xyIDs) = foldl' f a xyIDs

  mapGateReferences f (H xID) = H (f xID)
  mapGateReferences f (X xID) = X (f xID)
  mapGateReferences f (Y xID) = Y (f xID)
  mapGateReferences f (Z xID) = Z (f xID)
  mapGateReferences f (CNOT xID yID) = CNOT (f xID) (f yID)
  mapGateReferences f (CZ xID yID) = CZ (f xID) (f yID)
  mapGateReferences f (S xID) = S (f xID)
  mapGateReferences f (Sinv xID) = Sinv (f xID)
  mapGateReferences f (T xID) = T (f xID)
  mapGateReferences f (Tinv xID) = Tinv (f xID)
  mapGateReferences f (Swap xID yID) = Swap (f xID) (f yID)
  mapGateReferences f (Rz theta xID) = Rz theta (f xID)
  mapGateReferences f (Rx theta xID) = Rx theta (f xID)
  mapGateReferences f (Ry theta xID) = Ry theta (f xID)
  mapGateReferences f (Measure xID yID) = Measure (f xID) (f yID)
  mapGateReferences f (Reset xID) = Reset (f xID)
  mapGateReferences f (Uninterp name xyIDs) = Uninterp name (map f xyIDs)

data UnravelState g = (CircuitGraph g) => Unravel
  { accepted :: g,
    rejected :: g,
    currentMap :: Map (GateQubit (GraphGate g)) (GateQubit (GraphGate g)),
    fullMap :: Map (GateQubit (GraphGate g)) (Set (GateQubit (GraphGate g))),
    freshIDs :: [GateQubit (GraphGate g)]
  }

emptyUnravel :: (CircuitGraph g) => UnravelState g
emptyUnravel =
  Unravel
    { accepted = pureGates,
      rejected = pureGates,
      currentMap = Map.empty,
      fullMap = Map.empty,
      freshIDs = undefined
    }

-- Unravels a circuit with gates we can't interpret (according to a supplied
-- test, not just the "Uninterp" gate) so that the interpretable gates are in
-- one accepted circuit, and the uninterpretable ones are in a rejected
-- circuit. The inputs and outputs for the places where the circuit is cut out
-- are remapped to new qubits (with names taken from freshIDSource).

-- For example, suppose we have an algorithm that can't deal with H gates, and
-- we want to process

-- tof 1 2 3
-- H 3
-- cnot 3 2

-- The algorithm splits H 3 out into its own (rejected) graph, and relabels
-- its input as an output of the original circuit, and its output as an input.
-- This is slightly dangerous, in that the feedback between the graphs creates
-- the potential for a cycle that is locally invisible, so be careful.

-- The result looks like this, supposing our temp labels are prefixed with @:
-- Accepted:
--   tof 1 2 3
--   cnot @1 2
-- Rejected:
--   H @1
-- Name map: [(3, @1)]

-- To reconstruct the original circuit, the rejected gates must be put back
-- after the last unchanged reference in the accepted circuit, and before the
-- first relabeled reference. _All_ references in the rejected circuit should
-- be relabeled, so this condition should be meaningful and hold for every
-- reference in the rejected gate.

unravel ::
  (HasFeynmanControl, CircuitGraph g, CircuitGate (GraphGate g)) =>
  (GraphGate g -> Bool) ->
  [GateQubit (GraphGate g)] ->
  g ->
  (g, g, [(GateQubit (GraphGate g), Set (GateQubit (GraphGate g)))])
unravel testF freshIDSource gates =
  (accepted finState, rejected finState, Map.toList (fullMap finState))
  where
    finState = foldGates unravelAux (emptyUnravel {freshIDs = freshIDSource}) gates

    unravelAux st g =
      -- If the gate is accepted, map its references according to the current
      -- mapping, updating the current accept list
      -- If it's rejected, make new labels for all its references and map it
      -- according to the new mapping; update the list, mapping, fresh IDs
      if testF g
        then st {accepted = appendGate (accepted st) (mapGateReferences (currentMap st !) g)}
        else
          let (added, newMap, newFreshIDs) =
                relabelReferences g (currentMap st) (freshIDs st)
              addRefToSet m (refID, remapID) =
                Map.adjust (Set.insert remapID) refID m
           in st
                { rejected = appendGate (rejected st) (mapGateReferences (newMap !) g),
                  currentMap = newMap,
                  fullMap = foldl' addRefToSet (fullMap st) added,
                  freshIDs = newFreshIDs
                }

    initialMap = Map.fromList (zip allIDs allIDs)
    allIDs = Set.toList (foldReferences (flip Set.insert) Set.empty gates)

    -- Get new labels from freshIDs for every label referenced by this gate
    relabelReferences g m freshIDs =
      foldl'
        ( \(items, m', nextID : remainIDs) refID ->
            ((refID, nextID) : items, Map.insert refID nextID m', remainIDs)
        )
        ([], m, freshIDs)
        deps
      where
        deps = Set.toList (foldGateReferences (flip Set.insert) Set.empty g)

reknit :: [Primitive] -> [Primitive] -> [(ID, ID)] -> [Primitive]
reknit xGates yGates xyMap = undefined
