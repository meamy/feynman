{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use first" #-}

-- |
-- Module      : AncillaAware
-- Description : Extraction of unitary path sums to circuits, allowing creation and use of ancillae
-- Copyright   : (c) Matthew Amy, 2021, Joseph Lunderville, 2024
-- Maintainer  : matt.e.amy@gmail.com
-- Stability   : experimental
-- Portability : portable
module Feynman.Synthesis.Pathsum.AncillaAware where

import Control.Applicative ((<|>))
import Control.Exception (assert)
import Control.Monad (foldM, liftM, mapM, mfilter, msum, when, (>=>))
import Control.Monad.State.Strict (StateT, evalState, evalStateT, get, gets, put, runState)
import Control.Monad.Writer.Lazy (Writer, execWriter, runWriter, tell)
import Data.Bits (xor)
import Data.List (elemIndex, find, intercalate, sort, (\\))
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, mapMaybe, maybe)
import Data.Semigroup ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Debug.Trace
import Feynman.Algebra.Base
import Feynman.Algebra.Linear (F2Vec, bitI)
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)
import qualified Feynman.Algebra.Pathsum.Balanced as PS
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Control
import Feynman.Core (Angle (..), ID, Primitive (..), ccx, cs, dagger, removeSwaps)
import qualified Feynman.Core as Core
import Feynman.Synthesis.Pathsum.Clifford
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible
import qualified Feynman.Util.Unicode as U
import Feynman.Verification.Symbolic
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    chooseInt,
    generate,
    listOf,
    listOf1,
    oneof,
    quickCheck,
    resize,
    suchThat,
  )

{-----------------------------------
 Types
 -----------------------------------}

-- idx means IVar index, here
data AACtx = AACtx {ctxIDs :: [ID], ctxAncillae :: Map ID Int}

type ExtractionState a = StateT AACtx (Writer [ExtractionGates]) a

-- | Create a bidirectional context from a mapping from IDs to indices
fromCtx :: Int -> Map ID Int -> AACtx
fromCtx expectedOrd = flip (fromCtxWithAncillae expectedOrd) Set.empty

fromCtxWithAncillae :: Int -> Map ID Int -> Set ID -> AACtx
fromCtxWithAncillae expectedOrd ctx ancillae =
  assert (Set.isSubsetOf ancillae (Map.keysSet ctx)) $
    AACtx (reverse completeListRev) newAncillae
  where
    (completeListRev, newAncillae) =
      ascListToCompleteListWithAncillae
        0
        (Set.union (Map.keysSet ctx) ancillae)
        ([], Map.filterWithKey (\k v -> Set.member k ancillae) ctx)
        ((sort . map (\(a, b) -> (b, a))) (Map.toList ctx))

    ascListToCompleteListWithAncillae :: Int -> Set ID -> ([ID], Map ID Int) -> [(Int, ID)] -> ([ID], Map ID Int)
    ascListToCompleteListWithAncillae nextIdx idsSoFar (listProgressRev, ancillaeProgress) ascList
      -- Accounted for all variable IDs?
      | assert (nextIdx <= expectedOrd) (nextIdx == expectedOrd) =
          assert (null ascList) (listProgressRev, ancillaeProgress)
      -- Either no more explicit IDs, or we're convering a gap; generate a new ancilla
      | null ascList || (fst . head) ascList < nextIdx =
          let newID = newAncillaID idsSoFar nextIdx
           in ascListToCompleteListWithAncillae
                (nextIdx + 1)
                (Set.insert newID idsSoFar)
                (newID : listProgressRev, Map.insert newID nextIdx ancillaeProgress)
                ascList
      -- The only remaining case is an explicit ID, so expect that
      | assert ((fst . head) ascList == nextIdx) otherwise =
          let (idx, qID) : ascListRemain = ascList
           in ascListToCompleteListWithAncillae
                (nextIdx + 1)
                idsSoFar
                (qID : listProgressRev, Map.insert qID nextIdx ancillaeProgress)
                ascListRemain

newAncillaID :: Set ID -> Int -> ID
newAncillaID usedIDs searchIndex
  | Set.notMember tryID usedIDs = tryID
  | otherwise = newAncillaID usedIDs (searchIndex + 1)
  where
    tryID = "@" ++ show searchIndex

toIDMap :: AACtx -> Map ID Int
toIDMap (AACtx {ctxIDs = idList}) = Map.fromList (zip idList [0 ..])

-- | Deprecated, need a type class
daggerDep :: [ExtractionGates] -> [ExtractionGates]
daggerDep = reverse . map daggerGateDep
  where
    daggerGateDep g = case g of
      Hadamard _ -> g
      Phase a xs -> Phase (-a) xs
      MCT _ _ -> g
      Swapper _ _ -> g

{-----------------------------------
 Utilities
 -----------------------------------}

-- | ID for the ith variable
qref :: Int -> ExtractionState ID
qref i = gets ((!! i) . ctxIDs)

-- | index for a qubit ID
qidx :: ID -> ExtractionState Int
qidx q = gets (fromJust . elemIndex q . ctxIDs)

-- | Takes a map from Ints expressed as a list to a map on IDs
reindex :: [a] -> ExtractionState (Map ID a)
reindex = foldM go Map.empty . zip [0 ..]
  where
    go ctx (i, v) = do
      q <- qref i
      return $ Map.insert q v ctx

-- | Compute the variables in scope
ketToScope :: Pathsum DMod2 -> ExtractionState (Map Var ID)
ketToScope sop = foldM go Map.empty $ zip [0 ..] (outVals sop)
  where
    go ctx (i, p) = case solveForX p of
      [(v, 0)] -> do
        q <- qref i
        return $ Map.insert v q ctx
      _ -> return ctx

-- | Checks whether a variable is reducible
reducible :: Pathsum DMod2 -> Var -> Bool
reducible sop v = ppCondition && ketCondition
  where
    ppCondition = 0 == power 2 (quotVar v $ phasePoly sop)
    ketCondition = all (\p -> degree (quotVar v p) <= 0) $ outVals sop

-- | Compute the reducible variables in scope
reducibles :: Pathsum DMod2 -> Set Var
reducibles sop = snd $ foldr go (Set.empty, Set.empty) (outVals sop)
  where
    go p (seen, reducibles) = case solveForX p of
      [(v, 0)] | isP v && v `Set.notMember` seen -> (Set.insert v seen, Set.insert v reducibles)
      _ -> (Set.union seen (vars p), Set.difference reducibles (vars p))

-- | Computes a linearization of the ket by mapping monomials to unique variables
linearize :: (Ord v, Ord (PowerProduct v)) => [SBool v] -> ExtractionState AffineTrans
linearize xs = reindex $ evalState (mapM linearizePoly xs) (0, Map.empty)
  where
    linearizePoly f = foldM linearizeTerm (bitI 0 0, False) (toTermList f)
    linearizeTerm (bv, parity) (r, mono)
      | r == 0 = return (bv, parity)
      | degree mono == 0 = return (bv, parity `xor` True)
      | otherwise = do
          idx <- lookupMono mono
          return (bv `xor` bitI (idx + 1) idx, parity)
    lookupMono mono = do
      (maxBit, ctx) <- get
      case Map.lookup mono ctx of
        Just idx -> return idx
        Nothing -> do
          put (maxBit + 1, Map.insert mono maxBit ctx)
          return maxBit

-- | Computes a linearization of the ket by mapping monomials to unique variables
linearizeV2 :: (Ord v, Ord (PowerProduct v)) => [SBool v] -> ExtractionState AffineTrans
linearizeV2 xs =
  let supp = Set.toDescList . foldr (Set.union . Set.fromAscList . support) Set.empty $ xs
      ctx = Map.fromDescList $ zip supp [0 ..]
      k = length supp
      linearizePoly f = foldl linearizeTerm (bitI 0 0, False) (toTermList f)
      linearizeTerm (bv, parity) (r, mono)
        | r == 0 = (bv, parity)
        | degree mono == 0 = (bv, parity `xor` True)
        | otherwise = (bv `xor` bitI k (ctx ! mono), parity)
   in reindex $ map linearizePoly xs

-- | Changes the frame of a path-sum so that we have an output ket consisting
--   of only variables, e.g. |x>|y>|z>...
--
--   Returns the frame as well as the path-sum
changeFrame :: Pathsum DMod2 -> ([(Var, SBool Var)], Pathsum DMod2)
changeFrame sop = foldl go ([], sop) [0 .. outDeg sop - 1]
  where
    candidate (a, m) = a /= 0 && degree m > 0 && (degree m > 1 || not (all isF $ vars m))
    fv i = FVar $ "#tmp" ++ show i
    go (subs, sop) i = case (reverse . filter candidate . toTermList) $ outVals sop !! i of
      [] -> (subs, sop)
      (1, m) : xs ->
        let vs = Set.toList . vars $ ofMonomial m
            poly = outVals sop !! i
            psub = ofVar (fv i) + poly + ofMonomial m
         in ((fv i, poly) : subs, substitute vs psub sop)

-- | Reverts the frame of the path-sum back to the standard frame
revertFrame :: [(Var, SBool Var)] -> Pathsum DMod2 -> Pathsum DMod2
revertFrame = flip (foldl applySub)
  where
    applySub sop (v, p) = substitute [v] p sop

-- | Finds a simultaneous substitution y_i <- y + y_i such that P/y is Boolean
--
--   Exponential in the number of path variables
findSubstitutions :: [Var] -> Pathsum DMod2 -> Maybe (Var, [Var])
findSubstitutions xs sop = find go candidates
  where
    go (y, zs) =
      let sop' = foldr (\z -> substitute [z] (ofVar z + ofVar y)) sop zs
       in reducible sop' y
    pvars = map PVar [0 .. pathVars sop - 1]
    candidates = concatMap computeCandidatesI [1 .. length xs - 1]
    computeCandidatesI i = [(y, zs) | y <- reducibles, zs <- choose i $ pvars \\ [y]]
    choose 0 _ = [[]]
    choose i [] = []
    choose i (x : xs) = choose i xs ++ map (x :) (choose (i - 1) xs)
    reducibles = filter (isNothing . toBooleanPoly . flip quotVar (phasePoly sop)) xs

{-----------------------------------
 Passes
 -----------------------------------}

-- | Apply Clifford normalizations
normalize :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
normalize = return . grind

-- | Simplify the output ket up to affine transformations
--
--   Linearizes the ket as |A(x1...xk) + b> and then synthesizes
--   more or less a pseudoinverse of (A,b)
affineSimplifications :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
affineSimplifications sop = do
  output <- linearize $ outVals sop
  let circ = removeSwaps . dagger $ simplifyAffine output
  emitGates "Affine simplifications" $ map toMCT circ
  ctx <- gets toIDMap
  return $ sop .> computeActionInCtx circ ctx

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
phaseSimplifications :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplifications sop = do
  let (subs, localSOP) = changeFrame sop
  ctx <- ketToScope localSOP
  let poly = collectVars (Set.fromList . Map.keys $ ctx) $ phasePoly localSOP
  mapM_ synthesizePhaseTerm . toTermList . rename (ctx !) $ poly
  let localSOP' = localSOP {phasePoly = phasePoly localSOP - poly}
  return $ revertFrame subs localSOP'
  where
    synthesizePhaseTerm (a, m) =
      emitGates "Phase simplifications" [Phase (-a) (Set.toList $ vars m)]

-- | Simplify the output ket up to non-linear transformations
--
--   Applies reversible synthesis to eliminate non-linear terms where
--   possible
nonlinearSimplifications :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
nonlinearSimplifications sop = do
  ctx <- ketToScope sop
  foldM (simplifyState ctx) sop [0 .. outDeg sop - 1]
  where
    simplifyState ctx sop i = foldM (simplifyTerm ctx i) sop (toTermList $ outVals sop !! i)
    simplifyTerm ctx i sop term = case term of
      (0, _) -> return sop
      (_, m) | degree m <= 1 -> return sop
      (_, m) | not (vars m `Set.isSubsetOf` Map.keysSet ctx) -> return sop
      (_, m) | otherwise -> do
        target <- qref i
        let controls = map (ctx !) $ Set.toList (vars m)
        emitGates "Nonlinear simplications" [MCT controls target]
        return $ sop {outVals = addTermAt term i (outVals sop)}
    addTermAt term i xs =
      let (head, y : ys) = splitAt i xs
       in head ++ (y + ofTerm term) : ys

-- | Assuming the ket is in the form |A(x1...xn) + b>, synthesizes
--   the transformation |x1...xn> -> |A(x1...xn) + b>
finalize :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalize sop = do
  Debug.Trace.trace ("Finalizing " ++ show sop) (return ())
  ctx <- gets toIDMap
  foldM synthesizeMCTPoly sop (Map.keys ctx)
  where
    n = inDeg sop
    -- synthesizeAffineOnly :: ExtractionState (Pathsum DMod2)
    -- synthesizeAffineOnly = do
    --   ctx <- gets snd
    --   let input = Map.map (\i -> (bitI n i, False)) ctx
    --   let output = Map.map (\i -> bitvecOfPoly $ outVals sop !! i) ctx
    --   let circ = affineSynth input output
    --   emitGates "Finalize.affineOnly" $ map toMCT circ
    --   return $ sop .> computeActionInCtx circ ctx

    -- bitvecOfPoly p = (foldr xor (bitI 0 0) . map bitvecOfVar . Set.toList $ vars p, getConstant p == 1)
    -- bitvecOfVar (IVar i) = bitI n i
    -- bitvecOfVar (PVar _) = error "Attempting to finalize a proper path-sum!"
    -- bitvecOfVar (FVar _) = error "Attempting to extract a path-sum with free variables!"

    synthesizeMCTPoly :: Pathsum DMod2 -> ID -> ExtractionState (Pathsum DMod2)
    synthesizeMCTPoly synthSop outID = do
      AACtx {ctxIDs = idList, ctxAncillae = ancillaMap} <- gets id
      let outIdx = fromJust (elemIndex outID idList)
      let outPoly = outVals synthSop !! outIdx
      Debug.Trace.trace ("wastefulSynth " ++ show outID ++ " " ++ show outPoly) return ()
      when
        (isEasyAffinePoly (IVar outIdx) outPoly)
        (Debug.Trace.trace "  (why are we synthesizing this?)" (return ()))
      -- "outDeg synthSop" will be the index of the lowest-indexed bit in the
      -- renumbered thing (which is our ancilla) on the RHS of the tensor
      let ancI = outDeg synthSop
      -- find an unused variable name (i.e. ID) for the ancilla
      let ancID = newAncillaID (Set.fromList idList) ancI
      -- add the clean (constant 0) ancilla to synthSop
      let sopWithAnc = tensor synthSop (ket [constant 0])
      let newIDList = idList ++ [ancID]
      put (AACtx {ctxIDs = newIDList, ctxAncillae = Map.insert ancID ancI ancillaMap})
      -- This is kind of elegantly awful. We have a list of terms for
      -- this multilinear, and each term is a list of vars. Eventually
      -- we want to synthesize an MCT (i.e. multiply) for each term and
      -- CNOT (i.e. add) them together, because that's what a multilinear
      -- do. So we go terms -> get monomial -> get vars -> convert to
      -- list ...
      let termVars = map (Set.toList . vars . snd) (toTermList outPoly) :: [[Var]]
      -- ... -> then within each list of vars: get the index -> map via
      -- ctx to IDs; and finally -> MCT from each list of IDs.
      -- The controlled qubit is our clean ancilla.
      let computeGates = map (flip MCT ancID . map ((newIDList !!) . unI)) termVars :: [ExtractionGates]
      -- And finally we did this whole computation in the ancilla, so now
      -- swap the desired result with that (and the ancilla is
      -- incidentally garbage now, and we will not concern ourselves with
      -- it). The emitted gates are in reverse order, so the swap happens
      -- last even though we put it on the head. The computation is order
      -- independent, of course.
      let newGates = Swapper ancID outID : computeGates
      -- applyExtract is only reading ctx, we need to emitGates ourself
      emitGates "Finalize.wastefulSynth" newGates
      applyExtract sopWithAnc newGates

    -- find an unused ID (not in usedIDs) of the form "@<num>"
    findNewID usedIDs k =
      let tryID = '@' : show k
       in if Set.notMember tryID usedIDs
            then tryID
            else findNewID usedIDs (k + 1)

    -- if an output is just added together with other degree 1 terms, the
    -- output is trivial to generate with 0 or more CNOT -- probably affine
    -- synthesis should have taken care of these cases already
    isEasyAffinePoly :: (Ord v) => v -> SBool v -> Bool
    isEasyAffinePoly outID poly =
      let (_, terms) = unzip (toTermList poly)
          termVars = map vars terms
       in all ((== 1) . Set.size) termVars && any (Set.member outID) termVars

-- | Reduce the "strength" of the phase polynomial in some variable
--
--   Idea is to find a sequence of substitutions giving P' such that P'/y is Boolean.
--   This appears to be the difficult part of the problem. A simple heuristic is to
--   find some y such that 2P = yQ + R with Q Boolean and Q admits a "cover" of the form
--   where for every term x1...xk in Q, there exists i such that 2P = xi(x1...xk) + R'
--   Then for this cover we can apply the substitution xi <- xi + y, resulting in
--   2P' = yQ + yQ + Q + R'' = Q + R'' mod 2
--
--   Unfortunately this doesn't work for non-linear substitutions, e.g.
--     2P = x1x2y1 + x1y2
--   In this case, y2 <- y2 + x2y1 works.
--
--   More generally, say we have 2P = yQ + R. We want
--   to find some permutation [zi <- zi + Pi] such that
--     2P[zi <- zi + Pi] = R'
strengthReduction :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
strengthReduction sop = do
  ctx <- ketToScope sop
  let inScopePVars = filter isP . Map.keys $ ctx
  case findSubstitutions inScopePVars sop of
    Nothing -> return sop
    Just (y, xs) -> do
      let id_y = ctx ! y
      idx_y <- qidx id_y
      let applySubst sop x = case Map.lookup x ctx of
            Nothing -> return $ substitute [x] (ofVar y + ofVar x) sop
            Just id_x -> do
              idx_x <- qidx id_x
              emitGates "Strength reduction" [MCT [ctx ! y] (ctx ! x)]
              let f i = case i of
                    0 -> idx_y
                    1 -> idx_x
              return $
                substitute [x] (ofVar y + ofVar x) sop
                  .> embed cxgate (outDeg sop - 2) f f
      foldM applySubst sop xs

-- | Hadamard step
hLayer :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
hLayer sop = foldM go sop (zip [0 ..] $ outVals sop)
  where
    candidates = reducibles sop
    reducible v = isJust . toBooleanPoly . quotVar v $ phasePoly sop
    checkIt (v, p) = p == 0 && isP v && Set.member v candidates && reducible v
    go sop (i, p) = case filter checkIt (solveForX p) of
      [] -> return sop
      _ -> do
        q <- qref i
        emitGates "H layer" [Hadamard q]
        return $ sop .> embed hgate (outDeg sop - 1) (\0 -> i) (\0 -> i)

{-----------------------------------
 Synthesis
 -----------------------------------}

-- | Primitive to MCT gate
toMCT :: Primitive -> ExtractionGates
toMCT g = case g of
  CNOT c t -> MCT [c] t
  X t -> MCT [] t
  Swap x y -> Swapper x y
  _ -> error "Not an MCT gate"

-- | Push swaps to the end
pushSwaps :: [ExtractionGates] -> [ExtractionGates]
pushSwaps = reverse . snd . go (Map.empty, [])
  where
    get :: Map ID ID -> ID -> ID
    get ctx q = Map.findWithDefault q q ctx
    synthesize :: ID -> (Map ID ID, [ExtractionGates]) -> (Map ID ID, [ExtractionGates])
    synthesize q (ctx, acc) =
      let q' = get ctx q
       in if q' == q
            then (ctx, acc)
            else (Map.insert q' q' (Map.insert q (get ctx q') ctx), Swapper q q' : acc)
    go :: (Map ID ID, [ExtractionGates]) -> [ExtractionGates] -> (Map ID ID, [ExtractionGates])
    go (ctx, acc) [] = foldr synthesize (ctx, acc) $ Map.keys ctx
    go (ctx, acc) (x : xs) = case x of
      Hadamard q -> go (ctx, Hadamard (get ctx q) : acc) xs
      Phase a cs -> go (ctx, Phase a (map (get ctx) cs) : acc) xs
      MCT cs t -> go (ctx, MCT (map (get ctx) cs) (get ctx t) : acc) xs
      Swapper q1 q2 ->
        let (q1', q2') = (get ctx q1, get ctx q2)
         in go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs

{-----------------------------------
 Extraction
 -----------------------------------}

-- | A single pass of the synthesis algorithm
synthesizeFrontier :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizeFrontier sop = Debug.Trace.trace ("Synthesizing " ++ show sop) $ go (grind sop)
  where
    go sop
      | pathVars sop == 0 = synthesisPass sop >>= finalize
      | otherwise = synthesisPass sop >>= reducePaths
    synthesisPass =
      affineSimplifications
        >=> phaseSimplifications
        >=> nonlinearSimplifications
        >=> phaseSimplifications
    reducePaths sop = do
      sop' <- hLayer sop >>= normalize
      ( if pathVars sop' < pathVars sop
          then return sop'
          else strengthReduction sop' >>= synthesisPass >>= hLayer >>= normalize
        )

-- | Extract a Unitary path sum. Returns Nothing if unsuccessful
extractUnitary :: (HasFeynmanControl) => AACtx -> Pathsum DMod2 -> Maybe [ExtractionGates]
extractUnitary ctx sop = processWriter $ evalStateT (go sop) ctx
  where
    processWriter w = case runWriter w of
      (True, circ) -> Just $ daggerDep circ
      _ -> Nothing
    go sop = do
      sop' <- synthesizeFrontier sop
      ancillae <- gets ctxAncillae
      if pathVars sop' < pathVars sop
        then go sop'
        else
          let good = isTrivialUpToGarbage sop' (map snd (Map.toList ancillae))
           in Debug.Trace.trace
                (if good then "Resynthesis succeeded" else "Resynthesis failed: sop not trivial")
                (Debug.Trace.trace ("Trivial up to garbage: " ++ show sop' ++ "; ancillae " ++ show (map snd (Map.toList ancillae))) $ return good)

-- | Resynthesizes a circuit
resynthesizeCircuit :: (HasFeynmanControl) => [Primitive] -> [ID] -> Maybe [ExtractionGates]
resynthesizeCircuit xs ancillae =
  pushSwaps <$> extractUnitary (fromCtxWithAncillae (outDeg sop) ctx (Set.fromList ancillae)) sop
  where
    (sop, ctx) = runState (computeAction xs) Map.empty

emitGates :: (HasFeynmanControl) => String -> [ExtractionGates] -> ExtractionState ()
emitGates logDescription gates = traceIf $ tell gates
  where
    traceIf x =
      if ctlTraceResynthesis
        then Debug.Trace.trace (logDescription ++ ":\n  " ++ intercalate "\n  " (map show gates)) x
        else x

{-----------------------------------
 Testing
 -----------------------------------}

-- | Primitive to MCT gate
toExtraction :: Primitive -> ExtractionGates
toExtraction g = case g of
  CNOT c t -> MCT [c] t
  X t -> MCT [] t
  Swap x y -> Swapper x y
  H t -> Hadamard t
  Z t -> Phase (fromDyadic $ dyadic 1 0) [t]
  S t -> Phase (fromDyadic $ dyadic 1 1) [t]
  Sinv t -> Phase (fromDyadic $ dyadic 3 1) [t]
  T t -> Phase (fromDyadic $ dyadic 1 2) [t]
  Tinv t -> Phase (fromDyadic $ dyadic 7 2) [t]

-- | Retrieve the path sum representation of a primitive gate
extractionAction :: ExtractionGates -> Pathsum DMod2
extractionAction gate = case gate of
  Hadamard _ -> hgate
  Phase theta xs -> rzNgate theta $ length xs
  MCT xs _ -> mctgate $ length xs

-- | Apply a circuit to a state
applyExtract :: Pathsum DMod2 -> [ExtractionGates] -> ExtractionState (Pathsum DMod2)
applyExtract sop xs = do
  ctx <- gets toIDMap
  return $ foldl (absorbGate ctx) sop xs
  where
    absorbGate ctx sop gate =
      let index xs = ((Map.fromList $ zip [0 ..] [ctx ! x | x <- xs]) !)
       in case gate of
            Hadamard x -> sop .> embed hgate (outDeg sop - 1) (index [x]) (index [x])
            Swapper x y -> sop .> embed swapgate (outDeg sop - 2) (index [x, y]) (index [x, y])
            Phase theta xs ->
              sop
                .> embed
                  (rzNgate theta (length xs))
                  (outDeg sop - length xs)
                  (index xs)
                  (index xs)
            MCT xs x ->
              sop
                .> embed
                  (mctgate $ length xs)
                  (outDeg sop - length xs - 1)
                  (index $ xs ++ [x])
                  (index $ xs ++ [x])

extract :: ExtractionState a -> Int -> Map ID Int -> (a, [ExtractionGates])
extract st deg idMap = (runWriter . evalStateT st) (fromCtx deg idMap)

testCircuit :: [Primitive]
testCircuit = [H "y", CNOT "x" "y", T "y", CNOT "x" "y", H "x"]

bianCircuit :: [Primitive]
bianCircuit = circ ++ circ
  where
    circ =
      [ CNOT "x" "y",
        X "x",
        T "y",
        H "y",
        T "y",
        H "y",
        Tinv "y",
        CNOT "x" "y",
        X "x",
        T "y",
        H "y",
        Tinv "y",
        H "y",
        Tinv "y"
      ]

-- Need strength reduction
srCase :: [Primitive]
srCase = [CNOT "x" "y", H "x"] ++ cs "x" "y"

-- Need linear substitutions in the output for this case
hardCase :: [Primitive]
hardCase = [Tinv "y", CNOT "x" "y", H "x"] ++ cs "x" "y"

-- Need non-linear substitutions
harderCase :: Pathsum DMod2
harderCase =
  (identity 2 <> fresh)
    .> ccxgate
    .> hgate
    <> identity 2
      .> swapgate
    <> identity 1
      .> identity 1
    <> tgate
    <> tgate
      .> identity 1
    <> cxgate
      .> identity 2
    <> tdggate
      .> identity 1
    <> cxgate
      .> swapgate
    <> identity 1

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

-- QFT
qft :: Int -> [Primitive]
qft 1 = [H "x1"]
qft n = [H ("x" ++ show n)] ++ concatMap (go n) (reverse [1 .. (n - 1)]) ++ qft (n - 1)
  where
    go n i = crk (dMod2 1 (n - i)) ("x" ++ show i) ("x" ++ show n)
    crk theta x y =
      let angle = half * theta
       in [Rz (Discrete angle) x, Rz (Discrete angle) y, CNOT x y, Rz (Discrete $ -angle) y, CNOT x y]

qftFull :: Int -> [Primitive]
qftFull n = qft n ++ permute
  where
    permute = map (uncurry Swap) pairs
    pairs =
      zip
        ["x" ++ show i | i <- [0 .. (n - 1) `div` 2]]
        ["x" ++ show i | i <- reverse [(n + 1) `div` 2 .. (n - 1)]]

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
  arbitrary = fmap CliffordT $ resize maxGates $ listOf $ oneof gates
    where
      gates = [genH maxSize, genT maxSize, genCX maxSize]

-- | Variable names
var :: Int -> ID
var i = "q" ++ show i

-- | Random CX gate
genCX :: Int -> Gen Primitive
genCX n = do
  x <- chooseInt (0, n)
  y <- chooseInt (0, n) `suchThat` (/= x)
  return $ CNOT (var x) (var y)

-- | Random S gate
genT :: Int -> Gen Primitive
genT n = do
  x <- chooseInt (0, n)
  return $ T (var x)

-- | Random H gate
genH :: Int -> Gen Primitive
genH n = do
  x <- chooseInt (0, n)
  return $ H (var x)

-- | Checks that the path sum of a Clifford+T circuit is indeed Unitary
prop_Unitary_is_Unitary :: CliffordT -> Bool
prop_Unitary_is_Unitary (CliffordT xs) = isUnitary $ simpleAction xs

-- | Checks that frame change is reversible
prop_Frame_Reversible :: CliffordT -> Bool
prop_Frame_Reversible (CliffordT xs) = sop == revertFrame subs localSOP
  where
    sop = grind $ simpleAction xs
    (subs, localSOP) = changeFrame sop

-- | Checks that extraction always succeeds for a unitary path sum
prop_Clifford_plus_T_Extraction_Possible :: (HasFeynmanControl) => CliffordT -> Bool
prop_Clifford_plus_T_Extraction_Possible (CliffordT xs) = isJust (resynthesizeCircuit xs [])

-- | Checks that the translation from Clifford+T to MCT is correct
prop_Translation_Correct :: CliffordT -> Bool
prop_Translation_Correct (CliffordT xs) = grind sop == grind sop'
  where
    (sop, ctx) = runState (computeAction xs) Map.empty
    sop' = fst $ extract (applyExtract (identity $ Map.size ctx) (map toExtraction xs)) (outDeg sop) ctx

-- | Checks that affine simplifications are correct
prop_Affine_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Affine_Correctness (CliffordT xs) = grind sop' == grind sop''
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    (sop', gates) = extract (affineSimplifications sop) (outDeg sop) ctx
    (sop'', _) = extract (applyExtract sop gates) (outDeg sop) ctx

-- | Checks that phase simplifications are correct
prop_Phase_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Phase_Correctness (CliffordT xs) = grind sop' == grind sop''
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    (sop', gates) = extract (phaseSimplifications sop) (outDeg sop) ctx
    (sop'', _) = extract (applyExtract sop gates) (outDeg sop) ctx

-- | Checks that nonlinear simplifications are correct
prop_Nonlinear_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Nonlinear_Correctness (CliffordT xs) = grind sop' == grind sop''
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    (sop', gates) = extract (nonlinearSimplifications sop) (outDeg sop) ctx
    (sop'', _) = extract (applyExtract sop gates) (outDeg sop) ctx

-- | Checks that strength reduction is correct
prop_Strength_Reduction_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Strength_Reduction_Correctness (CliffordT xs) = grind sop' == grind sop''
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    (sop', gates) = extract (strengthReduction sop) (outDeg sop) ctx
    (sop'', _) = extract (applyExtract sop gates) (outDeg sop) ctx

-- | Checks that each step of the synthesis algorithm is correct
prop_Frontier_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Frontier_Correctness (CliffordT xs) = grind sop' == grind sop''
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    (sop', gates) = extract (synthesizeFrontier sop) (outDeg sop) ctx
    (sop'', _) = extract (applyExtract sop gates) (outDeg sop) ctx

-- | Checks that the overall algorithm is correct
prop_Extraction_Correctness :: (HasFeynmanControl) => CliffordT -> Bool
prop_Extraction_Correctness (CliffordT xs) = go
  where
    (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
    gates = extractUnitary (fromCtx (outDeg sop) ctx) sop
    go = case gates of
      Nothing -> True
      Just xs' ->
        let sop' = grind $ fst $ extract (applyExtract (identity $ outDeg sop) xs') (outDeg sop) ctx
         in sop == sop' || isTrivial (grind $ sop .> PS.dagger sop')

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

initialctx = Map.fromList $ zip [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] [0 ..]

-- | Generates a random Clifford+T circuit
generateCliffordT :: Int -> Int -> IO [Primitive]
generateCliffordT n k = generate customArbitrary
  where
    customArbitrary = resize k $ listOf1 $ oneof [genH n, genT n, genCX n]
