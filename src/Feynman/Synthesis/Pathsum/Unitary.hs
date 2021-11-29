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
import Data.List ((\\), find)
import Data.Map (Map, (!))
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Bits (xor)

import Control.Applicative ((<|>))
import Control.Monad (foldM, mapM, mfilter, liftM, (>=>), msum)
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

import Feynman.Core (ID, Primitive(..), Angle(..), dagger, cs, ccx)
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

-- | Changes the frame of a path-sum so that we have an output ket consisting
--   of only variables, e.g. |x>|y>|z>...
--
--   Returns the frame as well as the path-sum
changeFrame :: Pathsum DMod2 -> ([(Var, SBool Var)], Pathsum DMod2)
changeFrame sop = foldl go ([], sop) [0..outDeg sop - 1] where
  nonConstant (a,m) = a /= 0 && degree m > 0
  fv i              = FVar $ "#tmp" ++ show i
  go (subs, sop) i  = case filter nonConstant . toTermList $ (outVals sop)!!i of
    []                       -> (subs, sop)
    (1,m):[] | degree m == 1 -> (subs, sop)
    (1,m):xs                 ->
      let vs   = Set.toList . vars $ ofMonomial m
          poly = (outVals sop)!!i
          psub = ofVar (fv i) + poly - ofMonomial m
      in
        ((fv i, poly):subs, substitute vs psub sop)

-- | Reverts the frame of the path-sum back to the standard frame
revertFrame :: [(Var, SBool Var)] -> Pathsum DMod2 -> Pathsum DMod2
revertFrame = flip (foldl applySub) where
  applySub sop (v, p) = substitute [v] p sop

-- | Finds a simultaneous substitution y_i <- y + y_i such that P/y is Boolean
--
--   Exponential in the number of path variables
findSubstitutions :: [Var] -> PseudoBoolean Var DMod2 -> Maybe (Var, [Var])
findSubstitutions xs p = find go candidates where
  go (y, zs) = case foldr (+) (power 2 $ quotVar y p) [power 2 $ quotVar z p | z <- zs] of
    0 -> True
    _ -> False
  pvars      = filter isP $ Set.toList $ vars p
  candidates = concatMap computeCandidatesI [1..length xs - 1]
  computeCandidatesI i = [(y, zs) | y <- xs, zs <- choose i $ pvars \\ [y]]
  choose 0 _      = [[]]
  choose i []     = []
  choose i (x:xs) = (choose i xs) ++ (map (x:) $ choose (i-1) xs)

-- | Synthesize a multiply-controlled Toffoli gate
synthesizeMCT :: Int -> [ID] -> ID -> [Primitive]
synthesizeMCT _ [] t       = [X t]
synthesizeMCT _ [x] t      = [CNOT x t]
synthesizeMCT _ [x,y] t    = Core.ccx x y t
synthesizeMCT i (x:xs) t   = circ ++ Core.ccx x ("_anc" ++ show i) t ++ circ where
  circ = synthesizeMCT (i+1) xs ("_anc" ++ show i)

{-----------------------------------
 Passes
 -----------------------------------}

-- | Apply Clifford normalizations
normalize :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
normalize = return . normalizeClifford

-- | Simplify the output ket up to affine transformations
--
--   Linearizes the ket as |A(x1...xk) + b> and then synthesizes
--   more or less a pseudoinverse of (A,b)
affineSimplifications :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
affineSimplifications sop = do
  output <- linearize $ outVals sop
  let circ = simplifyAffine output
  tell $ dagger circ
  ctx <- gets snd
  return $ sop .> computeActionInCtx (dagger circ) ctx

-- | Simplify the phase polynomial by applying phase gates
--
--   We compute a local "frame" by writing the ket as |x1x2...xn>
--   and then re-writing the phase polynomial over x1...xn
--
--   TODO: This sometimes results in extra effort, particularly if the
--   substitution ends up increasing the number of terms in the phase
--   polynomial. This is because when p = x + p' and we substitute
--   p with y, we actually substitute x with y + p'. A better option
--   may be to factorize the phase polynomial as pQ + R and substitute
--   so that we have yQ + R, but this is a bit trickier and I need to check
--   whether this will break some cases...
phaseSimplifications :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplifications sop = do
  let (subs, localSOP) = changeFrame sop
  ctx <- ketToScope localSOP
  let poly = collectVars (Set.fromList . Map.keys $ ctx) $ phasePoly localSOP
  mapM_ synthesizePhaseTerm . toTermList . rename (ctx!) $ poly
  let localSOP' = localSOP { phasePoly = phasePoly localSOP - poly }
  return $ revertFrame subs localSOP'
  where synthesizePhaseTerm (a, m) = tell $ circ ++ [Rz (Discrete $ -a) "_t"] ++ circ where
          circ = synthesizeMCT 0 (Set.toList $ vars m) "_t"

-- | Simplify the output ket up to non-linear transformations
--
--   Applies reversible synthesis to eliminate non-linear terms where
--   possible
nonlinearSimplifications :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
nonlinearSimplifications = computeFixpoint where
  computeFixpoint sop = do
    sop' <- go sop
    if sop' == sop
      then return sop'
      else return sop'
  go sop = do
    ctx <- ketToScope sop
    foldM (simplifyState ctx) sop [0..outDeg sop - 1]
  scope = Set.fromList . Map.keys
  simplifyState ctx sop i = foldM (simplifyTerm ctx i) sop (toTermList $ (outVals sop)!!i)
  simplifyTerm ctx i sop term = case term of
    (0, _)                                               -> return sop
    (_, m) | degree m <= 1                               -> return sop
    (_, m) | not ((vars m) `Set.isSubsetOf` (scope ctx)) -> return sop
    (_, m) | otherwise                                   -> do
               target <- qref i
               let controls = map (ctx!) $ Set.toList (vars m)
               tell $ synthesizeMCT 0 controls target
               return $ sop { outVals = addTermAt term i (outVals sop) }
  addTermAt term i xs =
    let (head, y:ys) = splitAt i xs in
      head ++ (y + ofTerm term):ys

{-
-- | Simplify the output ket up to non-linear transformations
--
--   Applies reversible synthesis to eliminate non-linear terms where
--   possible
nonlinearSimplifications :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
nonlinearSimplifications = computeFixpoint where
  computeFixpoint sop = do
    sop' <- go sop
    if sop' == sop
      then return sop'
      else return sop'
  go sop = do
    ctx <- Debug.Trace.trace ("Computing scope") $ ketToScope sop
    foldM (simplifyState ctx) sop [0..outDeg sop - 1]
  scope = Set.fromList . Map.keys
  simplifyState ctx sop i = Debug.Trace.trace ("Simplifying entry " ++ show i) $ foldM (simplifyTerm ctx i) sop (toTermList $ (outVals sop)!!i)
  simplifyTerm ctx i sop term = Debug.Trace.trace ("simplifyNonlinear\nctx: " ++ show ctx ++ "\ni: " ++ show i ++ "\nsop: " ++ show sop ++ "\nterm: " ++ show term ++ "\n") $ case term of
    (0, _)                                               -> return sop
    (_, m) | degree m <= 1                               -> return sop
    (_, m) | not ((vars m) `Set.isSubsetOf` (scope ctx)) -> return sop
    (_, m) | otherwise                                   -> do
               target <- qref i
               let controls = Debug.Trace.trace ("Computing controls") $ map (ctx!) $ Set.toList (vars m)
               tell $ Debug.Trace.trace ("Synthesizing MCT (controls = " ++ show controls ++ ", target = " ++ show target) $ synthesizeMCT 0 controls target
               return $ Debug.Trace.trace ("Swapping out the output") $ sop { outVals = addTermAt term i (outVals sop) }
  addTermAt term i xs =
    let (head, y:ys) = splitAt i xs in
      head ++ (y + ofTerm term):ys
-}

-- | Assuming the ket is in the form |A(x1...xn) + b>, synthesizes
--   the transformation |x1...xn> -> |A(x1...xn) + b>
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

-- | Reduce the "strength" of the phase polynomial in some variable
--
--   Idea is to find a sequence of substitutions giving P' such that P'/y is Boolean.
--   This appears to be the difficult part of the problem. A simple heuristic is to
--   find some y such that 2P = yQ + R with Q Boolean and Q admits a "cover" of the form
--   where for every term x1...xk in Q, there exists i such that 2P = xi(x1...xk) + R'
--   Then for this cover we can apply the substitution xi <- xi + y, resulting in
--   2P' = yQ + yQ + Q + R'' = Q + R'' mod 2
strengthReduction :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
strengthReduction sop = do
  ctx <- ketToScope sop
  let scopedPVars = filter isP . Map.keys $ ctx
  case findSubstitutions scopedPVars (phasePoly sop) of
    Nothing      -> return sop
    Just (y, xs) -> do
      let id_y = ctx!y
      idx_y <- qidx id_y
      let applySubst sop x = case Map.lookup x ctx of
            Nothing   -> return $ substitute [x] (ofVar y + ofVar x) sop
            Just id_x -> do
              idx_x <- qidx id_x
              tell [CNOT (ctx!y) (ctx!x)]
              let f i = case i of
                    0 -> idx_y
                    1 -> idx_x
              return $ (substitute [x] (ofVar y + ofVar x) sop) .>
                       embed cxgate (outDeg sop - 2) f f
      foldM applySubst sop xs
  
-- | Hadamard step
hLayer :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
hLayer sop = foldM go sop (zip [0..] $ outVals sop) where
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

-- | A single pass of the synthesis algorithm
synthesizeFrontier :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizeFrontier sop = go (normalizeClifford sop) where
  go sop
    | pathVars sop == 0 = synthesisPass sop >>= finalize
    | otherwise         = synthesisPass sop
  synthesisPass = affineSimplifications >=>
                  phaseSimplifications >=>
                  nonlinearSimplifications >=>
                  phaseSimplifications >=>
                  strengthReduction >=>
                  hLayer >=>
                  normalize

-- | Extract a Unitary path sum. Returns Nothing if unsuccessful
--
--   Algorithm proceeds by Hadamard stages. In each stage
--     1. Normalize the path sum to get ket(x_1...x_n)
--     2. Synthesize P_{x_1...x_n}
--     3. Find some ket(x_i) such that P_{x_i} = x_i*Q(x...)
extractUnitary :: Ctx -> Pathsum DMod2 -> Maybe [Primitive]
extractUnitary ctx sop = processWriter $ evalStateT (go sop) ctx where
  processWriter w = case runWriter w of
    (True, circ) -> Just $ dagger circ
    _            -> Nothing
  go sop = do
    sop' <- synthesizeFrontier sop
    if pathVars sop' < pathVars sop
      then go sop'
      else return $ isTrivial sop'

-- | Resynthesizes a circuit
-- Ugh... Again we run into problems
resynthesizeCircuit :: [Primitive] -> Maybe [Primitive]
resynthesizeCircuit xs = extractUnitary (mkctx ctx) sop where
  (sop, ctx) = runState (computeAction xs) Map.empty

{-----------------------------------
 Testing
 -----------------------------------}

eval :: ExtractionState (Pathsum DMod2) -> Map ID Int -> Pathsum DMod2
eval st = fst . runWriter . evalStateT st . mkctx

testCircuit :: [Primitive]
testCircuit = [H "y", CNOT "x" "y", T "y", CNOT "x" "y", H "x"]

bianCircuit :: [Primitive]
bianCircuit = (circ ++ circ) where
  circ = [CNOT "x" "y", X "x", T "y", H "y", T "y", H "y", Tinv "y",
          CNOT "x" "y", X "x", T "y", H "y", Tinv "y", H "y", Tinv "y"]

-- Need linear substitutions in the output for this case
hardCase :: [Primitive]
hardCase = [CNOT "x" "y", H "x"] ++ cs "x" "y"

-- Need non-linear substitutions
harderCase :: Pathsum DMod2
harderCase = (identity 2 <> fresh) .>
             ccxgate .>
             hgate <> identity 2 .>
             swapgate <> identity 1 .>
             identity 1 <> tgate <> tgate .>
             identity 1 <> cxgate .>
             identity 2 <> tdggate .>
             identity 1 <> cxgate .>
             swapgate <> identity 1

-- Need linear substitutions that un-normalize the output ket.
-- This one is annoying because we effectively need to find some
-- linear substitution which will make one of the path variables reducible.
-- I don't have a more general way of handling this than to just look
-- for this particular case... yet
hardestCase :: [Primitive]
hardestCase = [H "x"] ++ cs "x" "y" ++ [H "y", CNOT "y" "x"]

-- This one is subtle. Only appears in certain configurations of the
-- context because normal forms are not unique for, and certain normal
-- form are irreducible. Simplest way to fix this is to fix the
-- irreducibility of those normal forms. Problem here is that
-- x0 + x1 + x2y0 is not computable in the final stage, but the variable y0
-- can be removed from the output by a computable transformation.
-- Alternatively, some changes of variables (hence some normalizations)
-- make this computable, but it may be possible to manufacture a situation
-- where this isn't possible. Curious
evenHarderCase :: [Primitive]
evenHarderCase = [CNOT "x" "z", H "x"] ++ ccx "x" "y" "z"

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

initialctx = Map.fromList $ zip [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] [0..]
ctx = mkctx $ initialctx
