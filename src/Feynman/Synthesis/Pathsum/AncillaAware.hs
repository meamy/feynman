{-|
Module      : Unitary
Description : Extraction of Unitary path sums to circuits
Copyright   : (c) Matthew Amy, 2021
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Synthesis.Pathsum.AncillaAware where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Bifunctor (first)
import Data.Foldable (foldl')
import Data.List ((\\), elemIndex, find, intercalate, isPrefixOf, sort)
import Data.Map (Map, (!))
import Data.Maybe (mapMaybe, fromMaybe, fromJust, maybe, isJust)
import Data.Semigroup ((<>))
import Data.Set (Set)
import Data.Tuple (swap)
import Data.Bits (xor)

import Control.Exception (assert)
import Control.Applicative ((<|>))
import Control.Monad (foldM, mapM, mfilter, liftM, (>=>), msum)
import Control.Monad.Writer.Lazy (Writer, tell, runWriter, execWriter)
import Control.Monad.State.Strict (StateT, get, gets, put, runState, evalState, evalStateT, modify)

import Test.QuickCheck (Arbitrary(..),
                        Gen,
                        quickCheck,
                        generate,
                        resize,
                        listOf,
                        listOf1,
                        suchThat,
                        chooseInt,
                        oneof)

import qualified Feynman.Core as Core

import Feynman.Control
import Feynman.Core (HasFeynmanControl, ID, Primitive(..), Angle(..), dagger, removeSwaps)
import Feynman.Circuits (cs, ccx)
import Feynman.Algebra.Base
import Feynman.Algebra.Linear (F2Vec, bitI)
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (dagger)
import qualified Feynman.Algebra.Pathsum.Balanced as PS

import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible
import Feynman.Synthesis.Pathsum.Clifford
import Feynman.Synthesis.Pathsum.Util

import qualified Feynman.Synthesis.XAG.Graph as XAG
import qualified Feynman.Synthesis.XAG.MinMultSat as XAG
import qualified Feynman.Synthesis.XAG.Simplify as XAG

import Feynman.Verification.Symbolic

traceAA :: (HasFeynmanControl) => String -> a -> a
traceAA = traceIf (ctlEnabled fcfTrace_Synthesis_Pathsum_Unitary)

traceValAA :: (HasFeynmanControl) => (a -> String) -> a -> a
traceValAA = traceValIf (ctlEnabled fcfTrace_Synthesis_Pathsum_Unitary)

{-----------------------------------
 Types
 -----------------------------------}

-- The ctxPrefixGen gives you a guaranteed-unique prefix (assuming you stick to
-- the system) to generate new ancilla names with. Every time you need a
-- prefix, take head from it and put tail back in the context monad for the
-- next function. nextGenPrefix is a great way to do this.
data AACtx = AACtx {ctxIDs :: [ID], ctxPrefixGen :: [ID]}

-- | Create a bidirectional context from a mapping from IDs to indices
mkctx :: Map ID Int -> AACtx
mkctx ctx = AACtx {ctxIDs = map snd . sort . map (\(a, b) -> (b, a)) . Map.toList $ ctx, ctxPrefixGen = ["@" ++ show i ++ "_" | i <- [0 ..]]}

type ExtractionState a = StateT AACtx (Writer [ExtractionGates]) a

nextGenPrefix :: ExtractionState (String)
nextGenPrefix = do
  prefixGen <- gets ctxPrefixGen
  case prefixGen of
    (prefix : remainingPrefixes) ->
      ( do
          modify (\m -> m {ctxPrefixGen = remainingPrefixes})
          return prefix
      )
    [] -> error "Infinite prefix source ran out????"

-- fromCtx is needed to convert the map of qubit names for a circuit to a list,
-- i.e. [ID], which is the internal format used by AACtx
fromCtx :: Int -> Map ID Int -> AACtx
fromCtx nQubits ctx = fromCtxWithAncillas nQubits ctx Set.empty

-- fromCtxWithAncillas additionally includes a set of ancillas, which here are just treated as extra names
fromCtxWithAncillas :: Int -> Map ID Int -> Set ID -> AACtx
fromCtxWithAncillas nQubits ctx ancillas =
  assert (Set.isSubsetOf ancillas (Map.keysSet ctx)) $
    assert (Set.isSubsetOf allGivenIDs (Set.fromList completeListRev)) $
      assert (all (\(k, i) -> if Map.member k ctx then i == ctx ! k else True) (zip (reverse completeListRev) [0 ..])) $
        AACtx (reverse completeListRev) prefixGen
  where
    completeListRev =
      fillListGaps 0 [] ((sort . map (\(a, b) -> (b, a))) (Map.toList ctx))

    -- Checks all qubit indexes to make sure there's a name assigned for each one
    fillListGaps :: Int -> [ID] -> [(Int, ID)] -> [ID]
    fillListGaps nextIdx listProgressRev ascList
      -- Accounted for all variable IDs?
      | assert (nextIdx <= nQubits) (nextIdx == nQubits) =
          assert (null ascList) listProgressRev
      -- Either no more explicit IDs, or we're convering a gap; generate a new name
      | null ascList || (fst . head) ascList < nextIdx =
          let newID = prefix ++ show nextIdx
           in fillListGaps (nextIdx + 1) (newID : listProgressRev) ascList
      -- The only remaining case is an explicit ID, assert that condition
      | assert ((fst . head) ascList == nextIdx) otherwise =
          let (idx, qID) : ascListRemain = ascList
           in fillListGaps (nextIdx + 1) (qID : listProgressRev) ascListRemain

    -- The generator for unique prefixes -- we need a prefix right away
    prefix : prefixGen = uniquePrefixes

    uniquePrefixes = filterCollisions nonUniquePrefixes plausibleCollisions []
      where
        filterCollisions (prefix : remainingPrefixes) [] checked =
          -- No collision! Return this and continue the list with checked
          -- swapping back to unchecked
          prefix : filterCollisions remainingPrefixes checked []
        filterCollisions prefixes@(prefix : remainingPrefixes) (checking : unchecked) checked
          -- Collision! Skip this prefix and keep looking, and since we won't
          -- generate this prefix again we can leave the collision we found off
          -- the list for the future
          | isPrefixOf prefix checking = filterCollisions remainingPrefixes (unchecked ++ checked) []
          -- No collision yet, but we need to keep looking -- just move the one
          -- we checked to the checked list
          | otherwise = filterCollisions prefixes unchecked (checking : checked)

        plausibleCollisions = [s | s <- Set.toList allGivenIDs, isPrefixOf "@" s]
        nonUniquePrefixes = ["@" ++ show i ++ "_" | i <- [0 ..]]

    allGivenIDs = Set.union (Map.keysSet ctx) ancillas

toIDMap :: AACtx -> Map ID Int
toIDMap (AACtx {ctxIDs = idList}) = Map.fromList (zip idList [0 ..])

-- | Deprecated, need a type class
daggerDep :: [ExtractionGates] -> [ExtractionGates]
daggerDep = reverse . map daggerGateDep where
  daggerGateDep g = case g of
    Hadamard _ -> g
    Phase a xs -> Phase (-a) xs
    MCT _ _    -> g
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

-- | Checks whether a variable is reducible
reducible :: Pathsum DMod2 -> Var -> Bool
reducible sop v = ppCondition && ketCondition where
  ppCondition  = 0 == power 2 (quotVar v $ phasePoly sop)
  ketCondition = all (\p -> degree (quotVar v p) <= 0) $ outVals sop

-- | Compute the reducible variables in scope
reducibles :: Pathsum DMod2 -> Set Var
reducibles sop = snd $ foldr go (Set.empty, Set.empty) (outVals sop) where
  go p (seen, reducibles) = case solveForX p of
    [(v,0)] | isP v && v `Set.notMember` seen -> (Set.insert v seen, Set.insert v reducibles)
    _                                         -> (Set.union seen (vars p), Set.difference reducibles (vars p))

-- | Computes a linearization of the ket by mapping monomials to unique variables
linearize :: (Ord v, Ord (PowerProduct v)) => [SBool v] -> ExtractionState AffineTrans
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

-- | Computes a linearization of the ket by mapping monomials to unique variables
linearizeV2 :: (Ord v, Ord (PowerProduct v)) => [SBool v] -> ExtractionState AffineTrans
linearizeV2 xs =
  let supp = Set.toDescList . foldr Set.union (Set.empty) . map (Set.fromAscList . support) $ xs
      ctx  = Map.fromDescList $ zip supp [0..]
      k    = length supp
      linearizePoly f = foldl linearizeTerm (bitI 0 0, False) (toTermList f)
      linearizeTerm (bv, parity) (r, mono)
        | r == 0           = (bv, parity)
        | degree mono == 0 = (bv, parity `xor` True)
        | otherwise        = (bv `xor` bitI k (ctx!mono), parity)
  in
    reindex $ map linearizePoly xs

-- | Changes the frame of a path-sum so that we have an output ket consisting
--   of only variables, e.g. |x>|y>|z>...
--
--   Returns the frame as well as the path-sum
changeFrame :: Pathsum DMod2 -> ([(Var, SBool Var)], Pathsum DMod2)
changeFrame sop = foldl go ([], sop) [0..outDeg sop - 1] where
  candidate (a,m)   = a /= 0 && degree m > 0 && (degree m > 1 || not (all isF $ vars m))
  fv i              = FVar $ "#tmp" ++ show i
  go (subs, sop) i  = case filter candidate . reverse . toTermList $ (outVals sop)!!i of
    []       -> (subs, sop)
    (1,m):xs ->
      let vs   = Set.toList . vars $ ofMonomial m
          poly = (outVals sop)!!i
          psub = ofVar (fv i) + poly + ofMonomial m
      in
        ((fv i, poly):subs, substitute vs psub sop)

-- | Reverts the frame of the path-sum back to the standard frame
revertFrame :: [(Var, SBool Var)] -> Pathsum DMod2 -> Pathsum DMod2
revertFrame = flip (foldl applySub) where
  applySub sop (v, p) = substitute [v] p sop

-- | Finds a simultaneous substitution y_i <- y + y_i such that P/y is Boolean
--
--   Exponential in the number of path variables
findSubstitutions :: [Var] -> Pathsum DMod2 -> Maybe (Var, [Var])
findSubstitutions xs sop = find go candidates where
  go (y, zs) =
    let sop' = foldr (\z -> substitute [z] (ofVar z + ofVar y)) sop zs in
      reducible sop' y
  pvars      = map PVar [0..pathVars sop - 1]
  candidates = concatMap computeCandidatesI [1..length xs - 1]
  computeCandidatesI i = [(y, zs) | y <- reducibles, zs <- choose i $ pvars \\ [y]]
  choose 0 _      = [[]]
  choose i []     = []
  choose i (x:xs) = (choose i xs) ++ (map (x:) $ choose (i-1) xs)
  reducibles      = filter (not . isJust . toBooleanPoly . (flip quotVar) (phasePoly sop)) xs

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
  let revCtx = (Map.fromList . map swap) (Map.toList ctx)

      synthesizePhaseTerm :: Pathsum DMod2 -> (DMod2, Monomial ID repr) -> ExtractionState (Pathsum DMod2)
      synthesizePhaseTerm ssop (a, m) = do
        emitGates "Phase simplifications" [Phase (-a) (Set.toList $ vars m)]
        let ssop' = ssop {phasePoly = phasePoly ssop - ofTerm (a, (Monomial . Set.map (revCtx !) . vars) m)}
        traceAA ("Simplified term " ++ show ssop ++ " - " ++ show "-> " ++ show ssop') $ return ()
        return ssop'

      shavePseudoBoolean :: PseudoBoolean ID DMod2 -> Int -> [(Int, SBool ID)]
      shavePseudoBoolean _ (-1) = []
      shavePseudoBoolean poly maxN =
        traceAA ("Shaving " ++ show poly ++ ", n = " ++ show maxN ++ ": got " ++ show sboolFrac ++ ", remainder " ++ show (poly - dyFrac)) $
          (maxN, sboolFrac) : shavePseudoBoolean (poly - dyFrac) (maxN - 1)
        where
          dyFrac = distribute (dMod2 1 maxN) sboolFrac
          sboolFrac = ofTermList (map (first (const 1)) oddNFracTerms)
          oddNFracTerms = filter (odd . numer. unpack . fst) nFracTerms
          nFracTerms = filter ((\(Dy _ dn) -> maxN == dn)  . unpack . fst) (toTermList poly)

  let poly = rename (ctx !) (collectVars (Set.fromList . Map.keys $ ctx) $ phasePoly localSOP)
  -- TODO document why the local frame transformation is done
  -- TODO consider splitting out synthesizePhasePolyNeg

  if ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_OriginalPhase
    then do
      localSOP' <- foldM synthesizePhaseTerm localSOP (toTermList poly)
      return $ revertFrame subs localSOP'
    else do
      prefix <- nextGenPrefix
      let maxN = foldr ((\(Dy a n) lastN -> max n lastN) . unpack . fst) 0 (toTermList poly)
          -- Shavings, because we iteratively subtract out binary polynomials
          -- for the pseudo-boolean, like shaving that precision level off,
          -- from the highest power of 1 / 2^n to the lowest.
          -- The takes a polynomial like 3 / 2^1 x_1 and separates it into
          -- (1 / 2^1)(x_1) + (1 / 2^0)(x_1)
          sboolShavings = [(prefix ++ "Rz" ++ show n, n, p) | (n, p) <- shavePseudoBoolean poly maxN, p /= 0]

          mctIDSet = foldl' (\idSet g -> case g of (MCT _ tID) -> Set.insert tID idSet; _ -> idSet) Set.empty

      traceAA ("Shaved " ++ show poly ++ ":" ++ concatMap (("\n  " ++) . show) sboolShavings) $ return ()
      let (qVars, _) = unzip (Map.toAscList ctx)
          sboolF = if ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase
                     then synthesizeSBoolsMCT
                     else if ctlEnabled fcfFeature_Synthesis_XAG_Direct
                            then synthesizeSBoolsXAG directXAGTransformers
                            else if ctlEnabled fcfFeature_Synthesis_XAG_Strash
                                   then synthesizeSBoolsXAG strashXAGTransformers
                                   else synthesizeSBoolsXAG minMultSatXAGTransformers
          sboolGates = sboolF prefix [(ancN, p) | (ancN, _, p) <- sboolShavings]
          phaseGates = [Phase (dMod2 (-1) n) [ancN] | (ancN, n, _ ) <- sboolShavings]
          ancIDSet = Set.union (mctIDSet sboolGates) (Set.fromList [ancN | (ancN, _, _ ) <- sboolShavings])
          rzGates = sboolGates ++ phaseGates -- ++ reverse sboolGates
      emitGates ("Phase SBools " ++ show sboolShavings) rzGates
      qIDs <- gets ctxIDs
      let createAnc = tensor (identity (outDeg sop)) (ket (replicate (Set.size ancIDSet) 0))
          sopAnc = times sop createAnc
          idMap = Map.fromList (zip (qIDs ++ Set.toAscList ancIDSet) [0 ..])
          sopAnc' = computeGates idMap sopAnc (rzGates ++ reverse sboolGates)
          sop' = grind (times sopAnc' (PS.dagger createAnc))
      traceAA "Phase synthesis debug" $ return ()
      traceAA ("  sop before phase synthesis:\n    " ++ show sop) $ return ()
      traceAA ("  sop substitutions: " ++ show subs) $ return ()
      traceAA ("  localSOP:\n    " ++ show localSOP) $ return ()
      traceAA ("  sop with ancillas (inDeg " ++ show (inDeg sopAnc) ++ "):\n    " ++ show sopAnc) $ return ()
      traceAA ("  ctxIDs:            " ++ show qIDs) $ return ()
      traceAA ("  idMap:             " ++ show ((map snd . sort . map (\(a,b) -> (b,a))) (Map.toList idMap))) $ return ()
      traceAA ("  sop with ancillas after phase synthesis:"
                        ++ fst (foldl' (\(str, s) g -> let s' = grind (computeGates idMap s [g])
                                                        in (str ++ "\n    " ++ show g ++ " -> " ++ show s', s'))
                                       ("", sopAnc) rzGates)) $ return ()
      traceAA ("  sop after phase synthesis:\n    " ++ show sop') $ return ()
      return sop'



-- | Simplify the output ket up to non-linear transformations
--
--   Applies reversible synthesis to eliminate non-linear terms where
--   possible
nonlinearSimplifications :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
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
               tell [MCT controls target]
               return $ sop { outVals = addTermAt term i (outVals sop) }
  addTermAt term i xs =
    let (head, y:ys) = splitAt i xs in
      head ++ (y + ofTerm term):ys

-- | Assuming the ket is in the form |A(x1...xn) + b>, synthesizes
--   the transformation |x1...xn> -> |A(x1...xn) + b>
finalize :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalize sop = do
  traceAA ("Finalizing (XAG) " ++ show sop) $ return ()
  qIDs <- gets ctxIDs
  -- The SBools in the path must at this point all be input variables ie IVar:
  -- finalize shouldn't be called if there are still path variables (PVar) and
  -- there definitely shouldn't be free FVar at all in this synthesis
  let idSBools = zip qIDs [rename (\(IVar i) -> qIDs !! i) sbool | sbool <- outVals sop]
  emitSBoolConstruction idSBools sop

emitSBoolConstruction :: (HasFeynmanControl) => [(ID, SBool ID)] -> Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
emitSBoolConstruction idSBools sop = do
  prefix <- nextGenPrefix
  let outQIDs = (Set.fromList . map fst) idSBools
      inQIDs = foldl' Set.union Set.empty (map (vars . snd) idSBools)
      qIDs = Set.toAscList (Set.union outQIDs inQIDs)
      synthGates = synthesizeSBools prefix idSBools

      -- mctIDs gets the target ID of any ExtractionGates synthesized.
      -- Note we don't implement all gates, classical synthesis doesn't use
      -- Hadamard or Phase
      mctIDs (MCT _ tID) = [tID]
      mctIDs _ = []

      dropRepeats xs = head xs : [y | (x, y) <- zip xs (tail xs), x /= y]

      -- computeGates wants all our IDs to have an index in the outVals of the
      -- Pathsum it's operating on, so start by making this mapping, and
      -- assigning IDs to all the ancillas whose existence we just implied
      synthQIDs =
        -- intermediate values should not overlap qubits
        assert (Set.disjoint (Set.fromList qIDs) (Set.fromList (concatMap mctIDs synthGates))) $
          qIDs ++ dropRepeats (concatMap mctIDs synthGates)

      -- Apply the actual synthesized gates to a (blank) pathsum
      synthSopWithGarbage =
        times
          (tensor (identity (inDeg sop)) (ket [0 | _ <- [1 .. length synthQIDs - inDeg sop]]))
          ( computeGates
              -- The labels assigned to the Pathsum qubits
              (Map.fromList (zip synthQIDs [0 ..]))
              -- The initial Pathsum -- pass inputs through, init ancillas to 0
              (identity (length synthQIDs))
              synthGates
          )

      -- Steal just the garbage output polynomials from sop, dropping the
      -- actual outputs
      garbageSBools =
        [ofVar (IVar i) | i <- [0 .. (inDeg sop - 1)]]
          ++ drop (outDeg sop) (outVals synthSopWithGarbage)

      -- What I want here is sort-of "compute garbageSBools", except I have
      -- SBool Var, not SBool ID, so that doesn't quite work. It's simpler to
      -- construct the Pathsum directly for now, but this isn't fantastically
      -- well-factored.
      -- Note we tweak inDeg/outDeg so it implicitly includes ancilla creation
      garbage =
        assert ((pathVars sop == 0) && (phasePoly sop == 0)) $
          Pathsum 0 (inDeg sop) (outDeg synthSopWithGarbage) 0 0 garbageSBools

      -- Glom (prepend) the garbage onto sop
      sopAwaitingGarbage = tensor sop (identity (outDeg garbage - inDeg sop))
      sopWithGarbage = times garbage sopAwaitingGarbage

      result = grind (times sopWithGarbage (PS.dagger synthSopWithGarbage))

  traceAA ("sopWithGarbage: " ++ show sopWithGarbage) $
    traceAA ("synthSopWithGarbage: " ++ show synthSopWithGarbage) $
      return ()

  emitGates "SBoolConstruction " (reverse synthGates)

  return result

-- | Synthesizes the transformation |x1...xn> -> |A(x1...xn) + b>, where
--   x1...xn are identified by a list of ID, and A(x1...xn) are identified by
--   a list of SBool Var. May imply the addition of many ancillas.
synthesizeSBools :: (HasFeynmanControl) => String -> [(ID, SBool ID)] -> [ExtractionGates]
synthesizeSBools
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_MCTKet = synthesizeSBoolsMCT
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGKet
      && ctlEnabled fcfFeature_Synthesis_XAG_Direct = synthesizeSBoolsXAG directXAGTransformers
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGKet
      && ctlEnabled fcfFeature_Synthesis_XAG_Strash = synthesizeSBoolsXAG strashXAGTransformers
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGKet
      && ctlEnabled fcfFeature_Synthesis_XAG_MinMultSat = synthesizeSBoolsXAG minMultSatXAGTransformers

synthesizeSBoolsMCT :: (HasFeynmanControl) => String -> [(ID, SBool ID)] -> [ExtractionGates]
synthesizeSBoolsMCT prefix idSBools =
  -- Synthesize computation of polynomial terms into ancillas
  concatMap sboolMcts idSBools
    ++ [Swapper (ancID qID) qID | (qID, _) <- idSBools]
  where
    sboolMcts (qID, sbool) =
      concat [termMCTs (ancID qID) val (Set.toList (vars term))
              | (val, term) <- toTermList sbool]
    termMCTs tID val termIDs
      | val == 0 = [MCT termIDs tID, MCT [] tID]
      | otherwise = [MCT termIDs tID]
    ancID qID = prefix ++ "M" ++ qID

directXAGTransformers = []

strashXAGTransformers = [XAG.mergeStructuralDuplicates]

minMultSatXAGTransformers :: (HasFeynmanControl) => [XAG.Graph -> XAG.Graph]
minMultSatXAGTransformers =
  [ XAG.mergeStructuralDuplicates,
    (\g -> fromMaybe g (XAG.resynthesizeMinMultSat g))
  ]

synthesizeSBoolsXAG :: (HasFeynmanControl) => [XAG.Graph -> XAG.Graph] -> String -> [(ID, SBool ID)] -> [ExtractionGates]
synthesizeSBoolsXAG transformers prefix idSBools =
  traceAA ("XAG before transformation: " ++ show rawXAG) $
    traceAA ("XAG transformed: " ++ show finXAG) $
      gates ++ copyOuts ++ swapOuts
  where
    swapOuts = [Swapper ancID qID | (ancID, (qID, _)) <- zip swapAncNames idSBools]
    copyOuts = [MCT [outID] ancID | (outID, ancID) <- zip outNames swapAncNames]

    swapAncNames = [prefix ++ "S" ++ show n | n <- [0 .. length outNames - 1]]

    (gates, outNames) = xagToMCTs prefix finXAG allInputs
    finXAG = foldr ($) rawXAG transformers
    rawXAG = XAG.Graph {XAG.nodes = rawNodes, XAG.inputIDs = rawInIDs, XAG.outputIDs = rawOutIDs}

    rawNodes :: [XAG.Node]
    rawOutIDs :: [Int]
    (rawNodes, rawOutIDs) = makeNodes firstFree idSBools
      where makeNodes :: Int -> [(ID, SBool ID)] -> ([XAG.Node], [Int])
            makeNodes startID [] = ([], [])
            makeNodes startID ((outID, sbool) : remain) =
              (sboolNodes ++ remainNodes, finTermID : remainOutIDs)
              where
                (remainNodes, remainOutIDs) = makeNodes nextStartID remain
                sboolNodes :: [XAG.Node]
                nextStartID :: Int
                (nextStartID, finTermID, sboolNodes) = makeSBoolNodes startID (toTermList sbool)

            makeSBoolNodes :: Int -> [(FF2, Monomial ID a)] -> (Int, Int, [XAG.Node])
            makeSBoolNodes allocID ((val, m) : remain) =
              (finAllocID, finTermID, termNodes ++ remainNodes)
              where
                (finAllocID, finTermID, remainNodes) =
                  makeSBoolNodesCont termAllocID termID remain
                (termAllocID, termID, termNodes) = makeTermNodes allocID (Set.toList (vars m))

            makeSBoolNodesCont allocID polyID [] = (allocID, polyID, [])
            makeSBoolNodesCont allocID polyID ((val, m) : remain)
              | val == 1 = (finAllocID, finTermID, termNodes ++ xorNode : invNodes ++ remainNodes)
              | otherwise = error "I thought inverted terms weren't used"
              where
                (finAllocID, finTermID, remainNodes) =
                  makeSBoolNodesCont (finPolyID + 1) finPolyID remain
                (finPolyID, invNodes) =
                  if val == 1 then (termAllocID, [])
                              else (termAllocID + 1, [XAG.Not (termAllocID + 1) termAllocID])
                xorNode = XAG.Xor termAllocID polyID termID
                (termAllocID, termID, termNodes) = makeTermNodes allocID (Set.toList (vars m))

            makeTermNodes :: Int -> [ID] -> (Int, Int, [XAG.Node])
            -- zero-length term disallowed
            makeTermNodes allocID (mID : remain) = makeTermNodesCont allocID (idMap ! mID) remain

            makeTermNodesCont allocID termID [] = (allocID, termID, [])
            makeTermNodesCont allocID termID (mID : remain) =
              (finAllocID, finTermID, XAG.And allocID termID (idMap ! mID) : remainNodes)
              where
                (finAllocID, finTermID, remainNodes) = makeTermNodesCont (allocID + 1) allocID remain

    rawInIDs = [2..(firstFree - 1)]
    firstFree = 2 + length allInputs
    idMap = Map.fromList (zip allInputs [2 ..])
    allInputs = Set.toAscList $
      foldr Set.union Set.empty
        (concatMap ((map (vars . snd) . toTermList) . snd) idSBools)

xagToMCTs :: (HasFeynmanControl) => String -> XAG.Graph -> [ID] -> ([ExtractionGates], [ID])
xagToMCTs prefix g qNames =
  -- qNames, outNames disjoint
  -- qNames labels every graph input
  assert (all (`Set.notMember` Set.fromList qNames) outNames) $
    assert (length (XAG.inputIDs g) == length qNames) $
      (gates, outNames)
  where
    outNames = map (idMap !) (XAG.outputIDs g)

    gates = concatMap nodeToMCTs (XAG.nodes g)

    nodeToMCTs :: XAG.Node -> [ExtractionGates]
    nodeToMCTs (XAG.Const nID False) = []
    nodeToMCTs (XAG.Const nID True) = [MCT [] (idMap ! nID)]
    nodeToMCTs (XAG.Not nID xID) = do
      let thisNode = idMap ! nID
          xNode = idMap ! xID
       in [MCT [xNode] thisNode, MCT [] thisNode]
    nodeToMCTs (XAG.And nID xID yID) = do
      let thisNode = idMap ! nID
          xNode = idMap ! xID
          yNode = idMap ! yID
       in [MCT [xNode, yNode] thisNode]
    nodeToMCTs (XAG.Xor nID xID yID) =
      let thisNode = idMap ! nID
          xNode = idMap ! xID
          yNode = idMap ! yID
       in [MCT [xNode] thisNode, MCT [yNode] thisNode]

    idMap = Map.fromList (zip (XAG.inputIDs g) qNames ++ nodeIDNames)
    nodeIDNames = [(nID, prefix ++ "X" ++ show nID) | nID <- nodeIDs]
    nodeIDs = map XAG.nodeID (XAG.nodes g)

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
strengthReduction :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
strengthReduction sop = do
  ctx <- ketToScope sop
  let inScopePVars = filter isP . Map.keys $ ctx
  case findSubstitutions inScopePVars sop of
    Nothing      -> return sop
    Just (y, xs) -> do
      let id_y = ctx!y
      idx_y <- qidx id_y
      let applySubst sop x = case Map.lookup x ctx of
            Nothing   -> return $ substitute [x] (ofVar y + ofVar x) sop
            Just id_x -> do
              idx_x <- qidx id_x
              tell [MCT [(ctx!y)] (ctx!x)]
              let f i = case i of
                    0 -> idx_y
                    1 -> idx_x
              return $ (substitute [x] (ofVar y + ofVar x) sop) .>
                       embed cxgate (outDeg sop - 2) f f
      foldM applySubst sop xs

-- | Hadamard step
hLayer :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
hLayer sop = foldM go sop (zip [0..] $ outVals sop) where
  candidates   = reducibles sop
  reducible v  = isJust . toBooleanPoly . quotVar v $ phasePoly sop
  checkIt (v,p) = p == 0 && isP v && Set.member v candidates && reducible v
  go sop (i,p) = case filter checkIt (solveForX p) of
    [] -> return sop
    _  -> do
      q <- qref i
      tell [Hadamard q]
      return $ sop .> embed hgate (outDeg sop - 1) (\0 -> i) (\0 -> i)

{-----------------------------------
 Synthesis
 -----------------------------------}

-- | Primitive to MCT gate
toMCT :: Primitive -> ExtractionGates
toMCT g = case g of
  CNOT c t -> MCT [c] t
  X t      -> MCT []  t
  Swap x y -> Swapper x y
  _        -> error "Not an MCT gate"

-- | Push swaps to the end
pushSwaps :: [ExtractionGates] -> [ExtractionGates]
pushSwaps = reverse . snd . go (Map.empty, []) where
  get :: Map ID ID -> ID -> ID
  get ctx q               = Map.findWithDefault q q ctx
  synthesize :: ID -> (Map ID ID, [ExtractionGates]) -> (Map ID ID, [ExtractionGates])
  synthesize q (ctx, acc) =
    let q' = get ctx q in
      if q' == q
      then (ctx, acc)
      else (Map.insert q' q' (Map.insert q (get ctx q') ctx), (Swapper q q'):acc)
  go :: (Map ID ID, [ExtractionGates]) -> [ExtractionGates] -> (Map ID ID, [ExtractionGates])
  go (ctx, acc) []        = foldr synthesize (ctx, acc) $ Map.keys ctx
  go (ctx, acc) (x:xs)    = case x of
    Hadamard q    -> go (ctx, (Hadamard $ get ctx q):acc) xs
    Phase a cs    -> go (ctx, (Phase a $ map (get ctx) cs):acc) xs
    MCT cs t      -> go (ctx, (MCT (map (get ctx) cs) (get ctx t)):acc) xs
    Swapper q1 q2 ->
      let (q1', q2') = (get ctx q1, get ctx q2) in
        go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs

{-----------------------------------
 Extraction
 -----------------------------------}

-- | A single pass of the synthesis algorithm
synthesizeFrontier :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizeFrontier sop =
  traceAA ("Synthesizing " ++ show sop) $
    go (grind sop)
  where
    go sop
      | pathVars sop == 0 = do
        traceAA ("finalizing, before synthesisPass: " ++ show sop) $ return ()
        sop' <- synthesisPass sop
        traceAA ("finalizing, after synthesisPass: " ++ show sop') $ return ()
        finalize sop'
      | otherwise = do
        traceAA ("reducing, before synthesisPass: " ++ show sop) $ return ()
        sop' <- synthesisPass sop
        traceAA ("reducing, after synthesisPass: " ++ show sop') $ return ()
        reducePaths sop'
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
      traceAA ("synthesizeFrontier returned " ++ show sop') $ return ()
      let pathVarsLeft = pathVars sop'
      if pathVarsLeft > 0 && pathVarsLeft < pathVars sop
        then go sop'
        else
          return $
            traceValAA
              (\t -> if t then "Resynthesis succeeded" else "Resynthesis failed: sop not trivial")
              (isTrivial sop')

-- | Resynthesizes a circuit
resynthesizeCircuit :: (HasFeynmanControl) => [Primitive] -> [ID] -> Maybe [ExtractionGates]
resynthesizeCircuit xs ancillas =
  pushSwaps <$> extractUnitary (fromCtxWithAncillas (outDeg sop) ctx (Set.fromList ancillas)) sop
  where
    (sop, ctx) = runState (computeAction xs) Map.empty

emitGates :: (HasFeynmanControl) => String -> [ExtractionGates] -> ExtractionState ()
emitGates logDescription gates =
  traceAA
    (logDescription ++ ":\n  " ++ intercalate "\n  " (map show gates))
    (tell gates)

computeGates :: (Foldable t) => Map ID Int -> Pathsum DMod2 -> t ExtractionGates -> Pathsum DMod2
computeGates ctx = foldl' (absorbGate ctx)

absorbGate :: Map ID Int -> Pathsum DMod2 -> ExtractionGates -> Pathsum DMod2
absorbGate ctx sop gate =
  let index xs = ((Map.fromList $ zip [0..] [ctx!x | x <- xs])!)
  in case gate of
    Hadamard x     -> sop .> embed hgate (outDeg sop - 1) (index [x]) (index [x])
    Swapper x y    -> sop .> embed swapgate (outDeg sop - 2) (index [x, y]) (index [x, y])
    Phase theta xs -> sop .> embed (rzNgate theta (length xs))
                                    (outDeg sop - length xs)
                                    (index xs)
                                    (index xs)
    MCT xs x       -> sop .> embed (mctgate $ length xs)
                                    (outDeg sop - length xs - 1)
                                    (index $ xs ++ [x])
                                    (index $ xs ++ [x])

