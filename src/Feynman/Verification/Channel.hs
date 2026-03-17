{-|
Module      : Channel
Description : General channel verification based on path sums
Copyright   : (c) Matthew Amy, 2026
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Verification.Channel where

import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.State.Strict
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set

import Feynman.Core hiding (dagger)
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced

-- This is mostly a re-write of Symbolic. Eventually they will be merged

{------------------------------------
 Path sum actions
 ------------------------------------}

-- Note: Density matrices |psi><psi| are stored as |rev psi*>|psi>
-- where rev denotes reversing the order of qubits. This is done
-- so that extending by a pure state is |phi*> tensor rho tensor |phi>
-- Indexing is hence n+i and n-1-i for the ith qubit and its conjugate

-- | Context for computing path sums of circuits
data Context = Context {
  sop   :: Pathsum DMod2,
  idx   :: Map ID Int,
  mixed :: Bool
  } deriving (Show)

-- | The empty context
emptyCtx :: Context
emptyCtx = Context (identity 0) Map.empty False

-- | The empty context
initialCtx :: [ID] -> [ID] -> Context
initialCtx vars inputs = Context sop ctx False where
  ctx = Map.fromList $ zip vars [0..]
  sop = ket [if x `elem` inputs then ofVar x else 0 | x <- vars]

-- | Retrieve the path sum representation of a primitive gate
unitaryAction :: Primitive -> Pathsum DMod2
unitaryAction gate = case gate of
  H _              -> hgate
  X _              -> xgate
  Y _              -> ygate
  Z _              -> zgate
  CNOT _ _         -> cxgate
  CZ _ _           -> czgate
  S _              -> sgate
  Sinv _           -> sdggate
  T _              -> tgate
  Tinv _           -> tdggate
  Swap _ _         -> swapgate
  Rz theta _       -> rzgate $ fromDyadic $ discretize theta
  Rx theta _       -> hgate * rzgate (fromDyadic $ discretize theta) * hgate
  Ry theta _       -> sdggate * hgate * rzgate (fromDyadic $ discretize theta) * hgate * sgate
  Ctrl _ g         -> controlled (unitaryAction g)
  Uninterp "CCZ" _ -> cczgate
  Uninterp "CCX" _ -> ccxgate
  Uninterp "MCZ" x -> mczgate (length x)
  Uninterp name _  -> error $ "gate " ++ name ++ " unsupported"
  _                -> error $ "gate " ++ show gate ++ " is not unitary"

-- | Gets the number of qubits
numQubits :: State Context Int
numQubits = gets (Map.size . idx)

-- | Find the relevant index or allocate one for the given qubit
findOrAlloc :: ID -> State Context Int
findOrAlloc x = do
  ctx <- get
  case Map.lookup x (idx ctx) of
    Just i  -> return i
    Nothing -> let i = Map.size (idx ctx) in do
      put ctx { sop = alloc (mixed ctx) (sop ctx),
                idx = Map.insert x i (idx ctx) }
      return i
  where alloc b sop = case b of
          True  -> ket [ofVar (x ++ "'")] <> sop <> ket [ofVar x]
          False -> sop <> ket [ofVar x]

-- | Converts a pure state to a mixed one
toMixed :: State Context ()
toMixed = do
  ctx <- get
  when (not $ mixed ctx) $
    put $ ctx { mixed = True, 
                sop = dual (sop ctx) <> (sop ctx) }
  where dual  = substVar primeF . conjugate . reverseOrder
        primeF (FVar v) = FVar $ v ++ "'"
        primeF v        = v

-- | Converts a pure state to a mixed one
toMixed' :: Context -> Context
toMixed' = execState toMixed

-- | Applies a primitive circuit component
applyPrimitive :: Primitive -> State Context ()
applyPrimitive gate = case gate of
  Measure x -> do
    i    <- findOrAlloc x
    n    <- numQubits
    toMixed
    let op = grind . applyMeasure (n+i) (n-1-i)
    modify $ \s -> s { sop = op $ sop s }
  Reset x -> do
    i    <- findOrAlloc x
    n    <- numQubits
    toMixed
    let op = grind . applyGate (epsilon .> fresh <> fresh) [n+i, n-1-i]
    modify $ \s -> s { sop = op $ sop s }
  _       -> do
    args <- mapM findOrAlloc $ getArgs gate
    n    <- numQubits
    b    <- gets mixed
    let op = let u = unitaryAction gate in
          case b of
            True  -> applyGate u (map (n+) args) . applyGate (conjugate u) (map (n-1-) args)
            False -> applyGate u args
    modify $ \s -> s { sop = op $ sop s }

-- | Simulates a circuit in a context
runCircuit :: [Primitive] -> State Context ()
runCircuit = sequence_ . map applyPrimitive

------------------------------------
-- Convenience operators
------------------------------------

-- | Apply a circuit to a given state
applyCircuit :: Pathsum DMod2 -> [Primitive] -> State Context (Pathsum DMod2)
applyCircuit st circ = modify (\s -> s{sop = st}) >> runCircuit circ >> gets sop

-- | Compute the path sum action of a primitive circuit
computeAction :: [Primitive] -> State Context (Pathsum DMod2)
computeAction xs = runCircuit xs >> gets sop

-- | Shortcut for computing an action in the empty context
simpleAction :: [Primitive] -> Pathsum DMod2
simpleAction = sop . (flip execState) emptyCtx . computeAction

-- | Computes the symbolic final state of a circuit
circuitAction :: [ID] -> [ID] -> [Primitive] -> Pathsum DMod2
circuitAction vars inputs = sop . (flip execState) (initialCtx vars inputs) . computeAction

-- | Closed version of complexAction
sopOfCircuit :: [ID] -> [ID] -> [Primitive] -> Pathsum DMod2
sopOfCircuit vars inputs = close . circuitAction vars inputs

{------------------------------------
 Verification methods
 ------------------------------------}

-- | The return type of verification queries
data Result =
    Equal
  | NotEqual String
  | Inconclusive (Pathsum DMod2)
  deriving (Show)

-- | Basic equivalence checking. Checks the miter if they're unitary, otherwise tries
--   to prove equivalence
validate :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> Result
validate global vars inputs c1 c2 = result where
  result = let init = initialCtx vars inputs
               ctx1 = execState (runCircuit c1) init
               ctx2 = execState (runCircuit c2) init
           in
             case not (mixed ctx1) && not (mixed ctx2) of
               True  -> checkMiter (sop ctx1) (sop ctx2)
               False -> checkEquality (sop $ toMixed' ctx1) (sop $ toMixed' ctx2)

  checkMiter sop1 sop2 = case f . grind $ sop1 .> dagger sop2 of
    Triv       -> Equal
    HHKill _ p -> NotEqual . show $ getSolution p
    _          -> Inconclusive $ f . grind $ sop1 .> dagger sop2

  checkEquality sop1 sop2 = case sop1 ~~* sop2 of
    True  -> Equal
    False -> NotEqual $ "  " ++ show sop1 ++ "\n  " ++ show sop2

  f = if global then dropGlobalPhase else id
