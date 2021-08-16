module Feynman.Optimization.PhaseFold where

import Data.List hiding (transpose)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Data.Bits

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase

{-- Phase folding optimization -}

data Ctx = Ctx {
  dim     :: Int,
  ket     :: Map ID (F2Vec, Bool),
  terms   :: Map F2Vec (Set (Loc, Bool), Angle),
  orphans :: [(Set (Loc, Bool), Angle)],
  phase   :: Angle
} deriving Show

{- Get the bitvector for variable v, or otherwise allocate one -}
getSt :: ID -> State Ctx (F2Vec, Bool)
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket' }
                  return (bv', False)
      where dim' = dim st + 1
            bv'  = bitI dim' (dim' - 1)
            ket' = Map.insert v (bv', False) (ket st)

{- Set the state of a variable -}
setSt :: ID -> (F2Vec, Bool) -> State Ctx ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv $ ket st }

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

{- Adds a mergeable phase term -}
addTerm :: Angle -> Loc -> (F2Vec, Bool) -> State Ctx ()
addTerm theta loc (bv, parity) = modify go where
  theta' = if bv == 0 then 0 else theta
  go st = case parity of
    False -> st { terms = Map.alter (add theta') bv $ terms st }
    True  -> st { terms = Map.alter (add (-theta')) bv $ terms st,
                  phase = phase st + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, parity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, parity), theta)
 
{- The Phase folding analysis -}
applyGate :: (Primitive, Loc) -> State Ctx ()
applyGate (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \(bv, b) -> setSt v (bv, Prelude.not b)
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (fst bv + fst bv', snd bv `xor` snd bv')
  CZ c t -> return ()  -- N-op wrt phase folding
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    mapM_ (\v -> modify $ exists v) args

{- Run the analysis on a circuit and state -}
runCircuit :: [Primitive] -> Ctx -> Ctx
runCircuit circ = execState (mapM_ applyGate $ zip circ [2..])

{- Generates an initial state -}
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = length inputs
  ket = zip (inputs ++ (vars \\ inputs)) [(bitI dim x, False) | x <- [0..]]

{- Run the analysis and merge phase gates -}
phaseFold :: [ID] -> [ID] -> [Primitive] -> [Primitive]
phaseFold vars inputs circ =
  let result = runCircuit circ $ initialState vars inputs
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
