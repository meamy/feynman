module Feynman.Optimization.PhaseFold where

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase

import Data.List hiding (transpose)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict

import Data.Bits

{-- Phase folding optimization -}
{- We have two options for implementation here:
 -
 -  1. Maintain a current state of each qubit
 -     over the standard basis. When a Hadamard
 -     gate is applied we then need to write all
 -     phases over the new standard basis.
 -     Cost: 1 XOR per CNOT,
 -           n^2 + n*num keys XORs per H
 -
 -  2. Express each phase as XORs over the current
 -     value of the qubits. Need some way to ensure
 -     the current values of all qubits forms a
 -     basis, otherwise might miss some collisions.
 -     Could map qubit IDs with unique values to unique
 -     indices. On application of a Hadamard we then
 -     only need to remove any phase with a 1 at the
 -     location the Hadamard was applied. Every CNOT
 -     triggers an update of all phases though
 -     Cost: num keys XORs/conditional bit flips per CNOT, 
 -           num keys bit tests per H -} 

data Ctx = Ctx {
  dim     :: Int,
  ket     :: Map ID (F2Vec, Bool),
  terms   :: Map F2Vec (Set (Loc, Bool), Angle),
  orphans :: [(Set (Loc, Bool), Angle)],
  phase   :: Angle
} deriving Show

type AI = State Ctx

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> AI (F2Vec, Bool)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket' }
                  return (bv', False)
      where dim' = dim st + 1
            bv'  = bitI dim' (dim' - 1)
            ket' = Map.insert v (bv', False) (ket st)

{- Existentially quantifies a variable. In particular, any term that no
 - longer has a representative becomes an "orphan" -- a term with
 - no current representative -}
exists :: ID -> Ctx -> Ctx
exists v st@(Ctx dim ket terms orphans phase) =
  let (vars, avecs) = unzip $ Map.toList $ Map.delete v ket
      (vecs, cnsts) = unzip avecs
      (t, o)        = Map.partitionWithKey (\b _ -> inLinearSpan vecs b) terms
      (dim', vecs') = addIndependent vecs
      avecs'        = zip vecs' $ cnsts ++ [False]
      orphans'      = (snd $ unzip $ Map.toList o) ++ orphans
      terms'        = if dim' > dim
                      then Map.mapKeysMonotonic (zeroExtend 1) t
                      else t
  in
    Ctx dim' (Map.fromList $ zip (vars ++ [v]) avecs') terms' orphans' phase

setSt :: ID -> (F2Vec, Bool) -> AI ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv $ ket st }

addTerm :: Angle -> Loc -> (F2Vec, Bool) -> AI ()
addTerm theta l (bv, parity) = modify go where
  go st = case parity of
    False -> st { terms = Map.alter (add theta) bv $ terms st }
    True  -> st { terms = Map.alter (add (-theta)) bv $ terms st,
                  phase = phase st + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (l, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (l, parity), theta)
 
{-- The main analysis -}
applyGate :: (Primitive, Loc) -> AI ()
applyGate (gate, l) = case gate of
  T v    -> getSt v >>= addTerm (Discrete $ dyadic 1 3) l
  Tinv v -> getSt v >>= addTerm (Discrete $ dyadic 7 3) l
  S v    -> getSt v >>= addTerm (Discrete $ dyadic 1 2) l
  Sinv v -> getSt v >>= addTerm (Discrete $ dyadic 3 2) l
  Z v    -> getSt v >>= addTerm (Discrete $ dyadic 1 1) l
  Rz p v -> getSt v >>= addTerm p l
  X v    -> getSt v >>= \(bv, b) -> setSt v (bv, Prelude.not b)
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (fst bv + fst bv', snd bv `xor` snd bv)
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    mapM_ (\v -> modify $ exists v) args

initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = zip (inputs ++ (vars \\ inputs)) [(bitI dim x, False) | x <- [0..]]
  
run :: [Primitive] -> Ctx -> Ctx
run circ = execState (mapM_ applyGate $ zip circ [2..])

phaseFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFold vars inputs circ =
  let result = run circ $ initialState vars inputs
      phases = (snd . unzip . Map.toList $ terms result) ++ (orphans result)
      (map, gphase) = foldr go (Map.empty, phase result) phases where
        go (locs, angle) (map, gphase) =
          let (loc, gphase', angle') = case Set.findMin locs of
                (l, False) -> (l, gphase, angle)
                (l, True)  -> (l, gphase + angle, (-angle))
              update (l,_) = Map.insert l (if loc == l then angle' else 0)
          in
            (Set.foldr update map locs, gphase')
      circ' = concatMap go (zip circ [2..]) where
        go (gate, l) = case Map.lookup l map of
          Nothing -> [(gate, l)]
          Just angle
            | angle == 0 -> []
            | otherwise  -> zip (synthesizePhase (getTarget gate) angle) [0..]
        getTarget gate = case gate of
          T x    -> x
          S x    -> x
          Z x    -> x
          Tinv x -> x
          Sinv x -> x
          Rz _ x -> x
  in
    (fst $ unzip $ circ') ++ (globalPhase (head vars) gphase)
