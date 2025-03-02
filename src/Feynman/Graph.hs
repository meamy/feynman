{-# LANGUAGE TypeOperators #-}

module Feynman.Graph where

import Control.Exception (assert)
import Control.Monad.State.Strict (State (..), evalState, gets)
import Data.Bifunctor (second)
import Data.Foldable (Foldable (..), foldl')
import Data.Kind (Type)
import Data.Map.Strict (Map, (!))
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Semigroup.Union
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Data.Tuple (swap)
import Feynman.Control
import Feynman.Core

traceG :: (HasFeynmanControl) => String -> a -> a
traceG = traceIf (ctlEnabled fcfTrace_Graph)

traceValG :: (HasFeynmanControl) => (a -> String) -> a -> a
traceValG = traceValIf (ctlEnabled fcfTrace_Graph)

class (Eq (GateQubit g), Ord (GateQubit g)) => CircuitGate g where
  type GateQubit g :: Type
  foldGateReferences :: (a -> GateQubit g -> a) -> a -> g -> a
  mapGateReferences :: (GateQubit g -> GateQubit g) -> g -> g

class
  (CircuitGate (GraphGate g), Eq (GateQubit (GraphGate g)), Ord (GateQubit (GraphGate g))) =>
  CircuitGraph g
  where
  -- type GraphQubit g :: Type
  type GraphGate g :: Type
  foldGates :: (a -> GraphGate g -> a) -> a -> g -> a
  foldReferences :: (a -> GateQubit (GraphGate g) -> a) -> a -> g -> a
  mapGates :: (GraphGate g -> GraphGate g) -> g -> g
  mapReferences :: (GateQubit (GraphGate g) -> GateQubit (GraphGate g)) -> g -> g
  pureGraph :: g
  appendGate :: g -> GraphGate g -> g
  graphFromList :: [GraphGate g] -> g
  graphFromList = foldl' appendGate pureGraph
  graphToList :: g -> [GraphGate g]
  graphToList = reverse . foldGates (flip (:)) []

-- In a way, it's nice that Haskell lets me do this.
-- In another way, it would be nicer if Feynman didn't use 3 different gate
-- representations, and I didn't feel like I had to do this.
instance (CircuitGate g) => CircuitGraph [g] where
  type GraphGate [g] = g
  foldGates = foldl'
  foldReferences f = foldl' (foldGateReferences f)
  mapGates = map
  mapReferences f = map (mapGateReferences f)
  pureGraph = []
  appendGate graph g = graph ++ [g]
  graphFromList = id
  graphToList = id

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
    rejected :: [(GraphGate g, [(GateQubit (GraphGate g), GateQubit (GraphGate g))])],
    unravelMapping :: Map (GateQubit (GraphGate g)) (GateQubit (GraphGate g)),
    freshIDs :: [GateQubit (GraphGate g)]
  }

-- Unravels a circuit with gates we can't interpret (according to a supplied
-- test, not just the "Uninterp" gate) so that the interpretable gates are in
-- one accepted circuit, and the uninterpretable ones are in a rejected list.
-- The inputs and outputs for the places where the circuit is cut out are
-- remapped to new qubits (with names taken from freshIDSource).

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
--   H 3, (3 -> @1)

-- To reconstruct the original circuit, the rejected gates must be put back
-- after the last unchanged reference in the accepted circuit, and before the
-- first relabeled reference. _All_ references in the rejected circuit should
-- be relabeled, so this condition should be meaningful and hold for every
-- reference in the rejected gate.

unravel ::
  (HasFeynmanControl, CircuitGraph g, CircuitGate (GraphGate g), Show g, Show (GraphGate g), Show (GateQubit (GraphGate g))) =>
  (GraphGate g -> Bool) ->
  [GateQubit (GraphGate g)] ->
  g ->
  (g, [(GraphGate g, [(GateQubit (GraphGate g), GateQubit (GraphGate g))])], [GateQubit (GraphGate g)])
unravel testF freshIDSource gates =
  (accepted finState, rejected finState, freshIDs finState)
  where
    finState = foldGates unravelAux initialUnravel gates
    initialUnravel =
      Unravel
        { accepted = pureGraph,
          rejected = [],
          unravelMapping = Map.fromList (zip allIDs allIDs),
          freshIDs = freshIDSource
        }
    allIDs = Set.toList (foldReferences (flip Set.insert) Set.empty gates)
    unravelAux st g =
      -- If the gate is accepted, map its references according to the current
      -- mapping, updating the current accept list
      -- If it's rejected, make new labels for all its references and map it
      -- according to the new mapping; update the list, mapping, fresh IDs
      if testF g
        then
          traceG ("Accepting " ++ show g) $
            st {accepted = appendGate (accepted st) (mapGateReferences (unravelMapping st !) g)}
        else
          traceG ("Rejecting " ++ show g) $
            let (added, newMap, newFreshIDs) =
                  relabelReferences g (unravelMapping st) (freshIDs st)
             in st
                  { rejected = (g, added) : rejected st,
                    unravelMapping = newMap,
                    freshIDs = newFreshIDs
                  }

    -- Get new labels from freshIDs for every label referenced by this gate
    relabelReferences g m freshIDs =
      traceValG (\(items, m', nextID : _) -> "Relabeling " ++ show g ++ " with " ++ show items ++ ", " ++ show m' ++ ", [" ++ show nextID ++ "..]") $
        foldl'
          ( \(items, m', nextID : remainIDs) refID ->
              ((refID, nextID) : items, Map.insert refID nextID m', remainIDs)
          )
          ([], m, freshIDs)
          (Set.toList (foldGateReferences (flip Set.insert) Set.empty g))

-- reknit just puts a graph back together that's been taken apart by unravel.
reknit ::
  (HasFeynmanControl, CircuitGraph g, CircuitGate (GraphGate g), Show g, Show (GraphGate g), Show (GateQubit (GraphGate g))) =>
  g ->
  [(GraphGate g, [(GateQubit (GraphGate g), GateQubit (GraphGate g))])] ->
  g
reknit unraveled stitchList =
  assert
    ( isJust $
        let allDisjoint (Just x) y | Set.disjoint x y = Just (Set.union x y)
            allDisjoint _ _ = Nothing
            stitchSets = [Set.fromList (map snd ms) | (_, ms) <- stitchList]
         in foldl' allDisjoint (Just Set.empty) stitchSets
    )
    $ knittedGraph (foldGates reknitAux initialReknit unraveled)
  where
    initialReknit =
      Reknit
        { knittedGraph = pureGraph,
          unappliedStitches = foldl' insertUnapplied Map.empty stitchList,
          reknitMapping = Map.fromList (foldReferences (\l x -> (x, x) : l) [] unraveled)
        }
    insertUnapplied m s@(_, rms) =
      assert (Set.disjoint (Set.fromList (map snd rms)) (Map.keysSet m)) $
        Map.union (Map.fromList (map (\(r, nr) -> (nr, s)) rms)) m
    reknitAux st gate
      | null stitchableRefs =
          st
            { knittedGraph =
                appendGate
                  (knittedGraph st)
                  (mapGateReferences (reknitMapping st !) gate)
            }
      | otherwise =
          let (removedGate, mappings) = unappliedStitches st ! Set.findMin stitchableRefs
              stitchMapping = Map.fromList (map swap mappings)
              newMapping = Map.union stitchMapping (reknitMapping st)
              stitchedGate = mapGateReferences (newMapping !) removedGate
           in assert (Set.disjoint (foldGateReferences (flip Set.insert) Set.empty stitchedGate) stitchableRefs) $
                reknitAux
                  ( st
                      { knittedGraph = appendGate (knittedGraph st) stitchedGate,
                        unappliedStitches =
                          foldl' (flip Map.delete) (unappliedStitches st) (map snd mappings),
                        reknitMapping = newMapping
                      }
                  )
                  gate
      where
        stitchableRefs =
          traceValG (\v -> "Stitchable: " ++ show v) $
            Set.intersection (Map.keysSet (unappliedStitches st)) refs
        refs =
          traceValG (\v -> "Refs: " ++ show v) $
            foldGateReferences (flip Set.insert) Set.empty gate

data ReknitState g = (CircuitGraph g) => Reknit
  { knittedGraph :: g,
    unappliedStitches :: Map (GateQubit (GraphGate g)) (GraphGate g, [(GateQubit (GraphGate g), GateQubit (GraphGate g))]),
    reknitMapping :: Map (GateQubit (GraphGate g)) (GateQubit (GraphGate g))
  }

gateReferenceSet :: (HasFeynmanControl, CircuitGate g) => g -> Set (GateQubit g)
gateReferenceSet = foldGateReferences (flip Set.insert) Set.empty

circuitReferenceSet :: (HasFeynmanControl, CircuitGraph g) => g -> Set (GateQubit (GraphGate g))
circuitReferenceSet = foldReferences (flip Set.insert) Set.empty

-- Check that:
-- 1. Both circuits reference the same set of qubits
-- 2. For each qubit, the subgraphs of each circuit including only gates
--    referencing that qubit are the same
equivalentToTrivialReorder :: (HasFeynmanControl, CircuitGraph g, CircuitGate (GraphGate g), Eq (GraphGate g)) => g -> g -> Bool
equivalentToTrivialReorder xCirc yCirc =
  (allRefsX == allRefsY) && all subgraphsMatch (Set.toList allRefsX)
  where
    subgraphsMatch ref = subgraphForRef xCirc ref == subgraphForRef yCirc ref
    subgraphForRef circ ref = foldGates (prependIfRef ref) [] circ
    prependIfRef ref soFar g
      | Set.member ref (gateReferenceSet g) = g : soFar
      | otherwise = soFar
    allRefsX = circuitReferenceSet xCirc
    allRefsY = circuitReferenceSet yCirc

makeFreshPrimitiveIDs :: [Primitive] -> [String]
makeFreshPrimitiveIDs graph =
  ["@" ++ show n | n <- [nextN ..]]
  where
    -- Scan the qubit names used by the graph, and find an n such that no ID
    -- with the prefix @(n + k), k >= 0, is in use -- this ensures no
    -- accidental overlap when we generate IDs
    nextN = foldReferences maxAncillaID 1 graph
    maxAncillaID n ('@' : name) = max n prefixN
      where
        prefixN = read ('0' : digitsPrefix) :: Int
        digitsPrefix = takeWhile (`Set.member` digits) name
    maxAncillaID n _ = n
    digits = Set.fromList "0123456789"
