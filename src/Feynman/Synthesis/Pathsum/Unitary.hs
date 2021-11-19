{-|
Module      : Unitary
Description : Extraction of Unitary path sums to circuits
Copyright   : (c) Matthew Amy, 2021
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Synthesis.Pathsum.Unitary where

import Data.Semigroup ((<>))
import Data.Maybe (mapMaybe, fromMaybe, fromJust, maybe, isJust)
import Data.List ((\\))
import Data.Map (Map, (!))
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Bits (xor)

import Control.Monad (foldM, mapM, mfilter, liftM, (>=>))
import Control.Monad.Writer.Lazy (Writer, tell, runWriter, execWriter)
import Control.Monad.State.Lazy (StateT, get, gets, put, runState, evalState, evalStateT)

import Test.QuickCheck (Arbitrary(..),
                        Gen,
                        quickCheck,
                        generate,
                        resize,
                        listOf,
                        suchThat,
                        chooseInt,
                        oneof)

import qualified Feynman.Core as Core

import Feynman.Core (ID, Primitive(..), Angle(..), dagger)
import Feynman.Algebra.Base
import Feynman.Algebra.Linear (F2Vec, bitI)
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)

import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible
import Feynman.Synthesis.Pathsum.Clifford

import Feynman.Verification.Symbolic

import Debug.Trace

{-----------------------------------
 Types
 -----------------------------------}

type Ctx = (Map Int ID, Map ID Int)
type ExtractionState a = StateT Ctx (Writer [Primitive]) a

-- | Create a bidirectional context from a mapping from IDs to indices
mkctx :: Map ID Int -> (Map Int ID, Map ID Int)
mkctx ctx = (Map.fromList . map (\(a, b) -> (b, a)) . Map.toList $ ctx, ctx)

{-----------------------------------
 Utilities
 -----------------------------------}

-- | ID for the ith variable
qref :: Int -> ExtractionState ID
qref i = gets ((!i) . fst)

-- | index for a qubit ID
qidx :: ID -> ExtractionState Int
qidx q = gets ((!q) . snd)

-- | Takes a map from Ints expressed as a list to a map on IDs
reindex :: [a] -> ExtractionState (Map ID a)
reindex = foldM go Map.empty . zip [0..] where
  go ctx (i, v) = do
    q <- qref i
    return $ Map.insert q v ctx

-- | Compute the variables in scope
ketToScope :: Pathsum DMod2 -> ExtractionState (Map Var ID)
ketToScope sop = foldM go Map.empty $ zip [0..] (outVals sop) where
  go ctx (i, p) = case solveForX p of
    [(v,0)] -> do
      q <- qref i
      return $ Map.insert v q ctx
    _       -> return ctx

-- | Computes a linearization of the ket by mapping monomials to unique variables
linearize :: Ord v => [SBool v] -> ExtractionState AffineTrans
linearize xs = reindex $ evalState (mapM linearizePoly xs) (0, Map.empty) where
  linearizePoly f = foldM linearizeTerm (bitI 0 0, False) (toTermList f)
  linearizeTerm (bv, parity) (r, mono)
    | r == 0           = return (bv, parity)
    | degree mono == 0 = return (bv, parity `xor` True)
    | otherwise        = do
        idx <- lookupMono mono
        return (bv `xor` bitI (idx + 1) idx, parity)
  lookupMono mono = do
    (maxBit, ctx) <- get
    case Map.lookup mono ctx of
      Just idx -> return idx
      Nothing  -> do
        put (maxBit + 1, Map.insert mono maxBit ctx)
        return maxBit

{-----------------------------------
 Passes
 -----------------------------------}

-- | Apply Clifford normalizations
normalize :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
normalize = return . normalizeClifford

-- | Simplify the output ket up to affine transformations
simplifyKet :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
simplifyKet sop = do
  output <- linearize $ outVals sop
  let circ = simplifyAffine output
  tell $ dagger circ
  ctx <- gets snd
  return $ sop .> computeActionInCtx (dagger circ) ctx

-- | Final affine simplifications needed to implement the operator
--   on the nose
finalize :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalize sop = do
  ctx <- gets snd
  let input = Map.map (\i -> (bitI n i, False)) ctx
  let output = Map.map (\i -> bitvecOfPoly $ (outVals sop)!!i) ctx
  let circ = affineSynth input output
  tell $ dagger circ
  ctx <- gets snd
  return $ sop .> computeActionInCtx (dagger circ) ctx
  where n = inDeg sop
        bitvecOfPoly p 
          | degree p > 1 = error "Attempting to finalize non-linear path-sum!"
          | otherwise    = (foldr xor (bitI 0 0) . map bitvecOfVar . Set.toList $ vars p,
                            getConstant p == 1)
        bitvecOfVar (IVar i) = bitI n i
        bitvecOfVar (PVar _) = error "Attempting to finalize a proper path-sum!"
        bitvecOfVar (FVar _) = error "Attempting to extract a path-sum with free variables!"

  
-- | Swap a (computable) state oracle to a phase oracle
stateToPhaseOracle :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
stateToPhaseOracle sop = do
  scopedVars <- liftM (Set.fromList . Map.keys) $ ketToScope sop
  let computableOracle (v,p) = p /= 0 && (vars p) `Set.isSubsetOf` scopedVars
  let go sop i = case filter computableOracle . solveForX $ (outVals sop)!!i of
        [] -> return sop
        _  -> do
          q <- qref i
          tell [H q]
          return $ sop .> embed hgate (outDeg sop - 1) (\0 -> i) (\0 -> i)
  foldM go sop [0..outDeg sop - 1]

-- | Phase oracle synthesis step
--
--   Needs to do a bit more work. Notably when |y>|x + z> is in the state and
--   2(yx + yz) is in the phase...
synthesizePhaseOracle :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizePhaseOracle sop = do
  ctx <- ketToScope sop
  let poly = collectVars (Set.fromList . Map.keys $ ctx) $ phasePoly sop
  mapM_ synthesizePhaseTerm . toTermList . rename (ctx!) $ poly
  return $ sop { phasePoly = phasePoly sop - poly }
  where synthesizePhaseTerm (a, m) = tell $ circ ++ [Rz (Discrete $ -a) "_t"] ++ circ where
          circ = synthesizeMCT 0 (Set.toList $ vars m) "_t"
        synthesizeMCT _ [] t       = [X t]
        synthesizeMCT _ [x] t      = [CNOT x t]
        synthesizeMCT _ [x,y] t    = Core.ccx x y t
        synthesizeMCT i (x:xs) t   = circ ++ Core.ccx x ("_anc" ++ show i) t ++ circ where
          circ = synthesizeMCT (i+1) xs ("_anc" ++ show i)

-- | Hadamard step
reducePaths :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
reducePaths sop = foldM go sop (zip [0..] $ outVals sop) where
  reducible v  = isJust . toBooleanPoly . quotVar v $ phasePoly sop
  go sop (i,p) = case filter (\(v,p) -> isP v && p == 0 && reducible v) $ solveForX p of
    [] -> return sop
    _  -> do
      q <- qref i
      tell [H q]
      return $ sop .> embed hgate (outDeg sop - 1) (\0 -> i) (\0 -> i)

{-----------------------------------
 Extraction
 -----------------------------------}

-- | Extract a Unitary path sum. Returns Nothing if unsuccessful
--
--   Algorithm proceeds by Hadamard stages. In each stage
--     1. Normalize the path sum to get ket(x_1...x_n)
--     2. Synthesize P_{x_1...x_n}
--     3. Find some ket(x_i) such that P_{x_i} = x_i*Q(x...)
extractUnitary :: Ctx -> Pathsum DMod2 -> Maybe [Primitive]
extractUnitary ctx sop = processWriter $ evalStateT (normalize sop >>= extract) ctx where
  processWriter w = case runWriter w of
    (Just _, circ) -> Just $ dagger circ
    _              -> Nothing
  extract sop
    | pathVars sop == 0 = extractReversible sop
    | otherwise         = do
        sop' <- synthesisPass sop
        if isTrivial sop'
          then return (Just ())
          else if pathVars sop' < pathVars sop then extract sop' else return Nothing
  extractReversible sop = do
    sop' <- synthesisPass sop >>= finalize
    if isTrivial sop'
      then return (Just ())
      else return Nothing
  synthesisPass = simplifyKet >=>
                  stateToPhaseOracle >=>
                  synthesizePhaseOracle >=>
                  reducePaths >=>
                  normalize

-- | Resynthesizes a circuit
-- Ugh... Again we run into problems
resynthesizeCircuit :: [Primitive] -> Maybe [Primitive]
resynthesizeCircuit xs = extractUnitary (mkctx ctx) sop where
  (sop, ctx) = runState (computeAction xs) Map.empty

{-----------------------------------
 Testing
 -----------------------------------}
testCircuit :: [Primitive]
testCircuit = [H "y", CNOT "x" "y", T "y", CNOT "x" "y", H "x"]

bianCircuit :: [Primitive]
bianCircuit = (circ ++ circ) where
  circ = [CNOT "x" "y", X "x", T "y", H "y", T "y", H "y", Tinv "y",
          CNOT "x" "y", X "x", T "y", H "y", Tinv "y", H "y", Tinv "y"]

{-----------------------------------
 Automated tests
 -----------------------------------}

-- | Maximum size of circuits
maxSize :: Int
maxSize = 9

-- | Maximum length of circuits
maxGates :: Int
maxGates = 100

-- | Type for generating instances of Clifford+T circuits
newtype CliffordT = CliffordT [Primitive] deriving (Show, Eq)

instance Arbitrary CliffordT where
  arbitrary = fmap CliffordT $ resize maxGates $ listOf $ oneof [genH, genT, genCX]

-- | Variable names
var :: Int -> ID
var i = "q" ++ show i

-- | Random CX gate
genCX :: Gen Primitive
genCX = do
  x <- chooseInt (0,maxSize)
  y <- chooseInt (0,maxSize) `suchThat` (/= x)
  return $ CNOT (var x) (var y)

-- | Random S gate
genT :: Gen Primitive
genT = do
  x <- chooseInt (0,maxSize)
  return $ T (var x)

-- | Random H gate
genH :: Gen Primitive
genH = do
  x <- chooseInt (0,maxSize)
  return $ H (var x)

-- | Checks that the path sum of a Clifford+T circuit is indeed Unitary
prop_Unitary_is_Unitary :: CliffordT -> Bool
prop_Unitary_is_Unitary (CliffordT xs) = isUnitary $ simpleAction xs

-- | Checks that the path sum of a Clifford+T circuit is correctly extracted
prop_Clifford_plus_T_Extraction_Possible :: CliffordT -> Bool
prop_Clifford_plus_T_Extraction_Possible (CliffordT xs) = isJust (resynthesizeCircuit xs)

{-
-- | Checks that the path sum of a Clifford+T circuit is correctly extracted
prop_Clifford_plus_T_Extraction_Correct :: CliffordT -> Bool
prop_Clifford_plus_T_Extraction_Correct (CliffordT xs) = go where
  go  = isTrivial . normalizeClifford . simpleAction $ xs ++ Core.dagger xs'
  xs' = resynthesizeCircuit xs
-}

q0 = "q0"
q1 = "q1"
q2 = "q2"
q3 = "q3"
q4 = "q4"
q5 = "q5"
q6 = "q6"
q7 = "q7"
q8 = "q8"
q9 = "q9"

ctx = mkctx $ Map.fromList $ zip [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] [0..]
