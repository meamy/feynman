{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : RelationalFold
Description : Relational phase folding optimization
Copyright   : (c) Matthew Amy, 2024
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable

Relational version of phase folding with applications to hybrid programs
-}

module Feynman.Optimization.RelationalFold where

import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Functor.Identity
import Data.Coerce
import Data.Bits

import Control.Monad.State.Strict hiding (join)

import Feynman.Core
import Feynman.Algebra.Base
import Feynman.Algebra.Linear
import Feynman.Synthesis.Phase
import Feynman.Optimization.ARD

import qualified Debug.Trace as Trace

{-----------------------------------
 Utilities
 -----------------------------------}

-- | Terms of the phase polynomial
type Term = (Set (Loc, Bool), Angle)

-- | Checks whether a bitvector is null
isNil :: F2Vec -> Bool
isNil = (== 0)

-- | Splits an affine parity into a bitvector and its affine part
split :: F2Vec -> (F2Vec, Bool)
split bv = (bv@@(width bv-2,0), bv@.(width bv - 1))

-- | Extends a bitvector by 0 on the left
extendLeft :: Int -> F2Vec -> F2Vec
extendLeft i = (flip shift) i . zeroExtend i

-- | Gets the parity bit (high-order bit)
getParity :: F2Vec -> Bool
getParity bv = bv@.(width bv - 1)

{-----------------------------------
 Optimization algorithm
 -----------------------------------}

-- | Context maintained during the analysis phase
data Ctx = Ctx {
  dim     :: Int,
  ket     :: Map ID F2Vec,
  terms   :: Map F2Vec Term,
  orphans :: [Term],
  phase   :: Angle
} deriving Show

-- | Get the (affine) parity for variable v, or otherwise allocate one
getSt :: ID -> State Ctx F2Vec
getSt v = get >>= \st ->
  case Map.lookup v (ket st) of
    Just bv -> return bv
    Nothing -> do put $ st { dim = dim', ket = ket', terms = terms' }
                  return (bv')
      where dim' = dim st + 1
            bv'  = bitI dim' 0
            ket' = Map.insert v bv' $ Map.map (extendLeft 1) (ket st)
            terms' = Map.mapKeysMonotonic (extendLeft 1) (terms st)

-- | Set the state of a variable as an (affine) parity
setSt :: ID -> F2Vec -> State Ctx ()
setSt v bv = modify $ \st -> st { ket = Map.insert v bv $ ket st }

-- | Increases the dimension (i.e. number of variables tracked)
alloc :: Int -> State Ctx ()
alloc i = modify go where
  go st = st { dim   = dim st + i,
               ket   = Map.map (extendLeft i) (ket st),
               terms = Map.mapKeysMonotonic (extendLeft i) (terms st) }

-- | Applies a rotation of a given angle on a particular (affine) parity
addTerm :: Angle -> Loc -> F2Vec -> State Ctx ()
addTerm theta loc aparity = modify go where
  theta' = if isNil aparity then 0 else theta
  go st = case split aparity of
    (parity, False) -> st { terms = Map.alter (add theta') parity $ terms st }
    (parity, True)  -> st { terms = Map.alter (add (-theta')) parity $ terms st,
                            phase = phase st + theta }
  add theta t = case t of
    Just (reps, theta') -> Just (Set.insert (loc, getParity aparity) reps, theta + theta')
    Nothing             -> Just (Set.singleton (loc, getParity aparity), theta)

-- | Abstract transformers for primitive gates
applyGate :: (Primitive, Loc) -> State Ctx ()
applyGate (gate, loc) = case gate of
  T v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 2) loc
  Tinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 7 2) loc
  S v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 1) loc
  Sinv v -> getSt v >>= addTerm (dyadicPhase $ dyadic 3 1) loc
  Z v    -> getSt v >>= addTerm (dyadicPhase $ dyadic 1 0) loc
  Rz p v -> getSt v >>= addTerm p loc
  X v    -> getSt v >>= \bv -> setSt v (complementBit bv (width bv - 1))
  CNOT c t -> do
    bv  <- getSt c
    bv' <- getSt t
    setSt t (bv + bv')
  CZ c t -> return ()  -- N-op wrt phase folding
  Swap u v -> do
    bv  <- getSt u
    bv' <- getSt v
    setSt u bv'
    setSt v bv
  _        -> do
    let args = getArgs gate
    _ <- mapM getSt args
    ctx <- get
    Trace.trace (show ctx) $ return ()
    alloc $ length args
    ctx' <- get
    Trace.trace (show ctx') $ return ()
    dim' <- gets dim
    mapM_ (\(v,i) -> setSt v $ bitI dim' i) $ zip args [0..]

{-----------------------------------
 Phase folding of the quantum WHILE
 -----------------------------------}

-- | Temporary, as we need vectors to have the same length here
initialState :: [ID] -> [ID] -> Ctx
initialState vars inputs = Ctx dim (Map.fromList ket) Map.empty [] 0 where
  dim = 1 + length inputs
  ket = (zip inputs [bitI dim x | x <- [0..]]) ++
        (zip (vars \\ inputs) [bitVec dim 0 | x <- [0..]])

-- | Fast forwards the analysis based on a summary
fastForward :: AffineRelation -> State Ctx ()
fastForward summary = do
  ctx <- get
  Trace.trace ("Ctx: \n" ++ show ctx) $ return ()
  Trace.trace ("summary: \n" ++ show summary) $ return ()
  let (ids, vecs) = unzip . Map.toList $ ket ctx
  let vecs' = vals $ compose' (makeExplicit . ARD . fromList $ vecs) summary
  let ket' = Map.fromList $ zip ids vecs'
  let dim' = width $ head vecs'
  let tms'  = Map.mapKeysMonotonic (extendLeft (dim' - dim ctx)) $ terms ctx
  let ctx'  = ctx { dim   = dim',
                    ket   = ket',
                    terms = tms' }
  Trace.trace ("Ctx': \n" ++ show ctx') $ return ()
  put $ ctx'

-- | Summarizes a conditional
branchSummary :: Ctx -> Ctx -> State (Ctx) AffineRelation
branchSummary ctx' ctx'' = do
  let o1  = orphans ctx' ++ Map.elems (terms ctx')
  let ar1 = makeExplicit . ARD . fromList . Map.elems $ ket ctx'
  let o2 = orphans ctx'' ++ Map.elems (terms ctx'')
  let ar2 = makeExplicit . ARD . fromList . Map.elems $ ket ctx''
  modify (\ctx -> ctx { orphans = orphans ctx ++ o1 ++ o2 } )
  return $ join ar1 ar2

-- | Summarizes a loop
loopSummary :: Ctx -> State (Ctx) AffineRelation
loopSummary ctx' = do
  modify (\ctx -> ctx { orphans = orphans ctx ++ orphans ctx' ++ (Map.elems $ terms ctx') })
  return $ star . projectTemporaries . makeExplicit . ARD . fromList . Map.elems $ ket ctx'
  --return $ starFF . makeExplicitFF . ARD . fromList . map (flip rotate (-1)) . Map.elems $ ket ctx'

-- | Abstract transformers for while statements
applyStmt :: WStmt -> State (Ctx) ()
applyStmt stmt = case stmt of
  WSkip _      -> return ()
  WGate l gate -> applyGate (gate, l)
  WSeq _ s1 s2 -> applyStmt s1 >> applyStmt s2
  WReset _ v   -> getSt v >>= \bv -> setSt v (bitVec (width bv) 0)
  WMeasure _ v -> getSt v >> return ()
  WIf _ s1 s2  -> do
    ctx <- get
    let vars  = Map.keys $ ket ctx
    let ctx'  = execState (applyStmt s1) $ initialState vars vars
    let ctx'' = execState (applyStmt s2) $ initialState vars vars
    summary <- branchSummary ctx' ctx''
    fastForward summary
  WWhile _ s   -> do
    ctx <- get
    let vars = Map.keys $ ket ctx
    let ctx' = execState (applyStmt s) $ initialState vars vars
    summary <- loopSummary ctx'
    fastForward summary

-- | Generate substitution list
genSubstList :: [ID] -> [ID] -> WStmt -> Map Loc Angle
genSubstList vars inputs stmt =

  let result = execState (applyStmt stmt) $ initialState vars inputs
      phases = (snd . unzip . Map.toList $ terms result) ++ orphans result
      gphase = phase result

      go (locs, angle) map =
        let (loc, angle') = case Set.findMin locs of
              (l, False) -> (l, angle)
              (l, True)  -> (l, (-angle))
            update (l,_) = Map.insert l (if loc == l then angle' else 0)
        in
          Set.foldr update map locs

  in
    Trace.trace ("Final state: \n" ++ show result) $ foldr go Map.empty phases

-- | Apply substitution list
applyOpt :: Map Loc Angle -> WStmt -> WStmt
applyOpt opts stmt = go stmt where
  go stmt = case stmt of
    WSkip l      -> WSkip l
    WGate l gate -> case Map.lookup l opts of
      Nothing    -> WGate l gate
      Just angle ->
        let gatelist = synthesizePhase (getTarget gate) angle in
          foldr (WSeq l) (WSkip l) $ map (WGate l) gatelist
    WSeq l s1 s2 -> WSeq l (go s1) (go s2)
    WReset l v   -> stmt
    WMeasure l v -> stmt
    WIf l s1 s2  -> WIf l (go s1) (go s2)
    WWhile l s   -> WWhile l (go s)

  getTarget gate = case gate of
    T x    -> x
    S x    -> x
    Z x    -> x
    Tinv x -> x
    Sinv x -> x
    Rz _ x -> x

-- | Optimization algorithm
phaseFoldpp :: [ID] -> [ID] -> WStmt -> WStmt
phaseFoldpp vars inputs stmt = applyOpt opts stmt where
  opts = genSubstList vars inputs stmt

-- Testing
vars = ["x", "y"]
testcase1 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WWhile 4 $ WGate 5 $ CNOT "x" "y") $
            WGate 6 $ Tinv "x"
test1 = genSubstList vars vars testcase1
test2 = execState (applyStmt testcase1) (initialState vars vars)

testcase2 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WIf 4 (WGate 5 $ CNOT "x" "y") (WSkip 6)) $
            WGate 7 $ Tinv "x"

testcase3 = WSeq 1 (WGate 2 $ T "x") $
            WSeq 3 (WReset 4 "x") $
            WGate 5 $ T "x"

testcase4 = WSeq 1 (WGate 2 $ CNOT "x" "y") $
            WSeq 3 (WGate 4 $ T "y") $
            WSeq 5 (WGate 6 $ CNOT "x" "y") $
            WSeq 7 (WWhile 8 $ WGate 9 $ Swap "x" "y") $
            WSeq 10 (WGate 11 $ CNOT "x" "y") $
            WSeq 12 (WGate 13 $ Tinv "y") $
            WGate 14 $ CNOT "x" "y"

testcase5 = WSeq 1 (WGate 2 $ T "y") $
            WSeq 3 (WWhile 4 $ WGate 5 $ H "x") $
            WGate 6 $ Tinv "y"

testcase6 = WSeq 1 (WGate 2 $ T "y") $
            WSeq 3 (WWhile 4 $
                    WSeq 5 (WGate 6 $ T "x") $
                    WWhile 7 $ (WGate 8 $ X "y")) $
            WGate 9 $ Tinv "y"