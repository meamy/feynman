{-|
Module      : Symbolic
Description : Symbolic verification based on path sums
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Verification.Symbolic where

import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Control.Monad.State.Strict
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Debug.Trace as Debug

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)

{------------------------------------
 Path sum actions
 ------------------------------------}

-- | Context for computing path sums of circuits
type Context = Map ID Int

-- | Retrieve the path sum representation of a primitive gate
primitiveAction :: Primitive -> Pathsum DMod2
primitiveAction gate = case gate of
  H _           -> hgate
  X _           -> xgate
  Y _           -> ygate
  Z _           -> zgate
  CNOT _ _      -> cxgate
  CZ _ _        -> czgate
  S _           -> sgate
  Sinv _        -> sdggate
  T _           -> tgate
  Tinv _        -> tdggate
  Swap _ _      -> swapgate
  Rz theta _    -> rzgate $ fromDyadic $ discretize theta
  Rx theta _    -> hgate * rzgate (fromDyadic $ discretize theta) * hgate
  Ry theta _    -> rzgate (fromDyadic $ discretize theta) * hgate * rzgate (fromDyadic $ discretize theta) * hgate
  Uninterp "CCZ" _  -> cczgate
  Uninterp _ _  -> error "Uninterpreted gates not supported"

-- | Find the relevant index or allocate one for the given qubit
findOrAlloc :: ID -> State Context Int
findOrAlloc x = do
  result <- gets $ Map.lookup x
  case result of
    Just i  -> return i
    Nothing -> gets Map.size >>= \i -> modify (Map.insert x i) >> return i

foldM' :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldM' _ z [] = return z
foldM' f z (x:xs) = do
  z' <- f z x
  z' `seq` foldM' f z' xs

-- | Apply a circuit to a state
applyCircuit :: Pathsum DMod2 -> [Primitive] -> State Context (Pathsum DMod2)
applyCircuit = foldM' absorbGate
  where sizeof = show . length . toTermList . phasePoly
        absorbGate sop gate = Debug.trace (sizeof sop) $ do
          args <- mapM findOrAlloc $ getArgs gate
          nOut <- gets Map.size
          let sop' = sop <> identity (nOut - outDeg sop)
          let g    = embed (primitiveAction gate)
                           (nOut - length args)
                           ((Map.fromList $ zip [0..] args)!)
                           ((Map.fromList $ zip [0..] args)!)
          return $ sop' .> g

-- | Create an initial state given a set of variables and inputs
makeInitial :: [ID] -> [ID] -> State Context ([SBool ID])
makeInitial vars inputs = fmap Map.elems $ foldM go Map.empty vars
  where go st x = do
          i <- findOrAlloc x
          if elem x inputs
            then return $ Map.insert i (ofVar x) st
            else return $ Map.insert i 0 st

-- | Compute the path sum action of a primitive circuit
computeAction :: [Primitive] -> State Context (Pathsum DMod2)
computeAction xs = do
  n <- gets Map.size
  applyCircuit (identity n) xs

-- | Shortcut for computing an action in the empty context
simpleAction :: [Primitive] -> Pathsum DMod2
simpleAction = (flip evalState) Map.empty . computeAction

-- | Shortcut for computing an action in a linear context
sopAction :: [ID] -> [Primitive] -> Pathsum DMod2
sopAction ids = (flip evalState) (Map.fromList $ zip ids [0..]) . computeAction

-- | Shortcut for computing an action in a context
computeActionInCtx :: [Primitive] -> Context -> Pathsum DMod2
computeActionInCtx xs = evalState (computeAction xs)

-- | Shortcut for computing an action given a set of variables and inputs
complexAction :: [ID] -> [ID] -> [Primitive] -> Pathsum DMod2
complexAction vars inputs circ = evalState st Map.empty where
  st = do
    init <- makeInitial vars inputs
    action <- computeAction circ
    return $ ket init .> action

strictAction :: [ID] -> [ID] -> [Primitive] -> Pathsum DMod2
strictAction vars inputs circ = foldl' applyGate inSt circ where
  n    = length vars
  inSt = ket [if v `elem` inputs then ofVar v else 0 | v <- vars]
  ctx  = Map.fromList $ zip vars [0..]
  applyGate sop gate = case gate of
    H x                     -> applyH sop (ctx!x)
    X x                     -> applyX sop (ctx!x)
    Z x                     -> applyZ sop (ctx!x)
    CNOT x y                -> applyCX sop (ctx!x) (ctx!y)
    CZ x y                  -> applyCZ sop (ctx!x) (ctx!y)
    S x                     -> applyS sop (ctx!x)
    Sinv x                  -> applySdg sop (ctx!x)
    T x                     -> applyT sop (ctx!x)
    Tinv x                  -> applyTdg sop (ctx!x)
    Swap x y                -> applySwap sop (ctx!x) (ctx!y)
    Uninterp "CCZ" [x,y,z]  -> applyCCZ sop (ctx!x) (ctx!y) (ctx!z)

{------------------------------------
 Verification methods
 ------------------------------------}

-- | The return type of verification queries
data Result =
    Identity
  | NotIdentity String
  | Inconclusive (Pathsum DMod2)
  deriving (Show)

-- These really need to be packaged up in a logic rather than separate
-- functions. Doing this for now until a better solution can be found.
-- Realistically this could also be done "application side" by composing
-- with relevant path sums.
validate :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> Result
validate global vars inputs c1 c2 =
  let sopWithContext = do
        st <- makeInitial vars inputs
        action <- computeAction $ c1 ++ dagger c2
        return $ ket st .> action .> bra st
      sop = f . grind $ evalState sopWithContext Map.empty where
        f = if global then dropGlobalPhase else id
  in
    case sop of
      Triv       -> Identity
      HHKill _ p -> NotIdentity . show $ getSolution p
      _          -> Inconclusive sop

validateExperimental :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> Result
validateExperimental global vars inputs c1 c2 =
  let sopWithContext = do
        st <- makeInitial vars inputs
        action <- computeAction $ c1 ++ dagger c2
        return $ action
      sop = f . grind $ evalState sopWithContext Map.empty where
        f = if global then dropGlobalPhase else id
  in
    case sop of
      Triv       -> Identity
      HHKill _ p -> NotIdentity . show $ getSolution p
      _          -> if isIdentity sop then Identity else NotIdentity "By explicit computation"

postselectAll :: [ID] -> State Context (Pathsum DMod2)
postselectAll xs = do
          args <- mapM findOrAlloc xs
          nOut <- gets Map.size
          return $ embed (bra $ map (\_ -> 0) args)
                         (nOut - length args)
                         ((Map.fromList $ zip [0..] args)!)
                         ((Map.fromList $ zip [0..] args)!)


validateWithPost :: Bool -> [ID] -> [ID] -> [Primitive] -> [Primitive] -> Result
validateWithPost global vars inputs c1 c2 =
  let sopWithContext = do
        st <- makeInitial vars inputs
        action <- computeAction $ c1 ++ dagger c2
        post <- postselectAll (vars \\ inputs)
        return $ ket st .> action .> post
      sop = f . dropAmplitude . grind $ evalState sopWithContext Map.empty where
        f = if global then dropGlobalPhase else id
  in
    if sop == ket (map ofVar . filter (`elem` inputs) $ vars)
    then Identity
    else case sop of
      HHKill _ p -> NotIdentity . show $ getSolution p
      _          -> Inconclusive sop
