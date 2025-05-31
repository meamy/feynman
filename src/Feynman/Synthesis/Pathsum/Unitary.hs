{-# LANGUAGE DataKinds #-}

{-|
Module      : Unitary
Description : Extraction of Unitary path sums to circuits
Copyright   : (c) Matthew Amy, 2021
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Synthesis.Pathsum.Unitary where

import Data.Bifunctor (first)
import Data.Bits (xor)
import Data.Foldable (foldl')
import Data.List ((\\), find, isPrefixOf)
import Data.Map (Map, (!))
import Data.Maybe (mapMaybe, fromMaybe, fromJust, maybe, isJust)
import Data.Semigroup ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Tuple (swap)

import Control.Applicative ((<|>))
import Control.Exception (assert)
import Control.Monad (foldM, mapM, mfilter, liftM, (>=>), msum)
import Control.Monad.Writer.Lazy (Writer, tell, runWriter, execWriter)
import Control.Monad.State.Strict (StateT, get, gets, put, runState, evalState, evalStateT)

import qualified Debug.Trace

import qualified Feynman.Core as Core

import Feynman.Core (ID, Primitive(..), Angle(..), dagger, removeSwaps, HasFeynmanControl)
import Feynman.Control
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
import Feynman.Synthesis.Reversible.XAG (inputSavingXAGSynth, minimizeXAG, inputErasingXAGSynth)
import qualified Feynman.Synthesis.XAG.Graph as XAG
import qualified Feynman.Synthesis.XAG.MinMultSat as XAG
import qualified Feynman.Synthesis.XAG.Simplify as XAG
import Feynman.Synthesis.XAG.Util (fromSBools)
import Feynman.Verification.Symbolic

{-----------------------------------
 Types
 -----------------------------------}

data Ctx = Ctx {indexToID :: Map Int ID, idToIndex :: Map ID Int, curPrefixI :: Int}
type ExtractionState a = StateT Ctx (Writer [ExtractionGates]) a

-- | Create a bidirectional context from a mapping from IDs to indices
mkctx :: Map ID Int -> Ctx
mkctx ctx = Ctx (Map.fromList . map (\(a, b) -> (b, a)) . Map.toList $ ctx) ctx 1

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

freshPrefix :: ExtractionState ID
freshPrefix = do
  st <- get
  let curI = curPrefixI st
  let ctx = idToIndex st
  let pfx = show curI ++ "A"
  put (st { curPrefixI = curI + 1 })
  case Map.lookupGE pfx ctx of
    Nothing -> return pfx
    Just (used, _) -> if not (pfx `isPrefixOf` used) then return pfx else freshPrefix

-- | ID for the ith variable
qref :: Int -> ExtractionState ID
qref i = gets ((! i) . indexToID)

-- | index for a qubit ID
qidx :: ID -> ExtractionState Int
qidx q = gets ((! q) . idToIndex)

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

-- | Apply a circuit to a state
applyExtract :: Pathsum DMod2 -> [ExtractionGates] -> ExtractionState (Pathsum DMod2)
applyExtract sop xs = do
  ctx <- gets idToIndex
  return $ foldl (absorbGate ctx) sop xs
  where absorbGate ctx sop gate =
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

emitGates :: (HasFeynmanControl) => Pathsum DMod2 -> [ExtractionGates] -> ExtractionState (Pathsum DMod2)
emitGates sop gates = do
  st <- get
  let ancillaIDs = Set.toList (Set.fromList (concatMap (filter (`Map.notMember` idToIndex st) . targetIDs) gates))
  let n = outDeg sop
  let m = length ancillaIDs
  traceU ("  emit - ancillaIDs: " ++ show ancillaIDs) $ return ()
  let ctx = foldr (uncurry Map.insert) (idToIndex st) (zip ancillaIDs [outDeg sop..])
  let revCtx = foldr (uncurry Map.insert) (indexToID st) (zip [outDeg sop..] ancillaIDs)
  put (st { idToIndex = ctx, indexToID = revCtx })
  tell gates
  traceU ("  emitting:\n" ++ unlines (map (("    " ++) . show) gates)) $ return ()
  let extendedSOP = tensor sop (ket (replicate m 0))
  extendedSOP' <- applyExtract extendedSOP gates
  let sop' = grind $ times extendedSOP' (tensor (identity n) (bra (replicate m 0)))
  put st
  -- And return the modified sop with our circuit applied: hopefully identity
  return $ traceU ("  after apply: " ++ show sop') sop'
  where targetIDs (MCT _ tgt) = [tgt]
        targetIDs (Phase _ _) = []
        targetIDs (Swapper tgtA tgtB) = [tgtA, tgtB]
        targetIDs (Hadamard tgt) = [tgt]

traceU :: (HasFeynmanControl) => String -> a -> a
traceU msg val
  | ctlEnabled fcfTrace_Synthesis_Pathsum_Unitary = Debug.Trace.trace msg val
  | otherwise = val

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
affineSimplifications :: Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
affineSimplifications sop = do
  output <- linearize $ outVals sop
  let circ = removeSwaps . dagger $ simplifyAffine output
  tell $ map toMCT circ
  ctx <- gets idToIndex
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
phaseSimplifications sop
  | phasePoly (grind sop) == 0 = return sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_MCRzPhase = phaseSimplificationsMCRz sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_MCTRzPhase = phaseSimplificationsMCTRz sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGRzPhase = phaseSimplificationsXAGRz sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGMBURzPhase = phaseSimplificationsXAGMBURz sop

phaseSimplificationsMCRz :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplificationsMCRz sop = do
  let (subs, localSOP) = changeFrame sop
  ctx <- ketToScope localSOP
  let poly = collectVars (Set.fromList . Map.keys $ ctx) $ phasePoly localSOP
  mapM_ synthesizePhaseTerm . toTermList . rename (ctx!) $ poly
  let localSOP' = localSOP { phasePoly = phasePoly localSOP - poly }
  return $ revertFrame subs localSOP'
  where synthesizePhaseTerm (a, m) = tell [Phase (-a) (Set.toList $ vars m)]

-- Shaving, because we iteratively subtract out binary polynomials for the
-- pseudo-boolean, like shaving that precision level off, from the highest
-- power of 1 / 2^n to the lowest.
-- This takes e.g. 3 / 2^1 x_1 and separates it into a sum of components,
-- (1 / 2^1)(x_1) and (1 / 2^0)(x_1) in this case.
shavePseudoBoolean :: (HasFeynmanControl) => PseudoBoolean ID DMod2 -> Int -> [(Int, SBool ID)]
shavePseudoBoolean _ (-1) = []
shavePseudoBoolean poly maxN =
  traceU ("Shaving " ++ show poly ++ ", n = " ++ show maxN ++ ": got " ++ show sboolFrac ++ ", remainder " ++ show (poly - dyFrac)) $
    (maxN, sboolFrac) : shavePseudoBoolean (poly - dyFrac) (maxN - 1)
  where
    dyFrac = distribute (dMod2 1 maxN) sboolFrac
    sboolFrac = ofTermList (map (first (const 1)) oddNFracTerms)
    oddNFracTerms = filter (odd . numer. unpack . fst) nFracTerms
    nFracTerms = filter ((\(Dy _ dn) -> maxN == dn)  . unpack . fst) (toTermList poly)

-- | Returns a list of triples of (suggested qubit ID, power, pseudo-boolean)
--
--   See the definition of shavePseudoBoolean for info about how the phase
--   polynomial shaved; essentially for each "shaving" you want to apply phase
--   of -e^(2 * pi * i / (2 ^ power)), controlled by the pseudo-boolean, to
--   cancel the phase polynomial of the pathsum.
shavePhase :: (HasFeynmanControl) => Pathsum DMod2 -> ID -> ExtractionState [(ID, Int, SBool ID)]
shavePhase sop prefix = do
  -- We don't need the subs because we update the pathsum by evaluating
  -- TODO document why the local frame transformation is done
  let (_, localSOP) = changeFrame sop
  localCtx <- ketToScope localSOP
  let poly = rename (localCtx !) (collectVars (Set.fromList . Map.keys $ localCtx) $ phasePoly localSOP)
  let maxN = foldr ((\(Dy a n) lastN -> max n lastN) . unpack . fst) 0 (toTermList poly)
  let sboolShavings = [(prefix ++ "Rz" ++ show n, n, p) | (n, p) <- shavePseudoBoolean poly maxN, p /= 0]
  traceU ("Shaved " ++ show poly ++ ":" ++ concatMap (("\n  " ++) . show) sboolShavings) $ return ()
  traceU ("Phase SBools " ++ show sboolShavings) $ return ()
  return sboolShavings

phaseSimplificationsMCTRz :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplificationsMCTRz sop = do
  prefix <- freshPrefix
  sboolShavings <- shavePhase sop prefix
  let phaseGates = [Phase (dMod2 (-1) n) [ancN] | (ancN, n, _ ) <- sboolShavings]
  let sboolMCTs targetID sbool = [MCT (Set.toList (vars term)) targetID | (_, term) <- toTermList sbool]
  let sboolGates = concat [sboolMCTs ancN p | (ancN, _, p) <- sboolShavings]
  let sboolDagGates = reverse sboolGates
  let rzGates = sboolGates ++ phaseGates ++ sboolDagGates
  emitGates sop rzGates

phaseSimplificationsXAGRz :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplificationsXAGRz sop = do
  prefix <- freshPrefix
  ctx <- gets idToIndex
  revCtx <- gets indexToID
  sboolShavings <- shavePhase sop prefix
  let phaseGates = [Phase (dMod2 (-1) n) [ancN] | (ancN, n, _ ) <- sboolShavings]
  let sbools = [rename (IVar . (ctx !)) sbool | (_, _, sbool) <- sboolShavings]
  traceU ("Phase SBools, using IVars " ++ show sbools) $ return ()
  let xag = minimizeXAG (fromSBools (inDeg sop) sbools)
  let (xagGates, _) = inputSavingXAGSynth xag (Map.elems revCtx) [ancN | (ancN, _, _ ) <- sboolShavings] [prefix ++ show i | i <- [1..]]
  let xagDagGates = reverse xagGates
  let rzGates = xagGates ++ phaseGates ++ xagDagGates
  emitGates sop rzGates

phaseSimplificationsXAGMBURz :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
phaseSimplificationsXAGMBURz sop = do
  prefix <- freshPrefix
  ctx <- gets idToIndex
  sboolShavings <- shavePhase sop prefix
  let phaseGates = [Phase (dMod2 (-1) n) [ancN] | (ancN, n, _ ) <- sboolShavings, n > 0]
  -- TODO 1: special case, any -1/2^0 terms can be implemented as MCRz gates directly... don't include those in the XAG
  -- maybe this only makes sense for terms that break down into CZ (as opposed to MCZ)?
  -- so we could be left with a (different) -1/2^0 polynomial
  -- let phaseGates = -- TODO 1.1 not correct yet -- [Phase (dMod2 (-1) n) [ancN] | (ancN, n, _ ) <- sboolShavings, n == 0]
  let xagSBools = [rename (IVar . (ctx !)) sbool | (_, n, sbool) <- sboolShavings, n > 0]
  let xag = minimizeXAG (fromSBools (length sboolShavings) )
  let (xagGates, _) = inputSavingXAGSynth xag [] [ancN | (ancN, _, _ ) <- sboolShavings] [prefix ++ show i | i <- [1..]]
  -- TODO 2: implement MBU for xagDagGates here
  -- TODO 2.1: this is a sequence of H, measure, then use the measured qubit
  -- TODO 2.2: the measured qubit has to classically control a CZ gate
  -- TODO 2.3: the CZ is applying f(x), except there's going to be more than one CZ --
  -- we have to factor out vars from the polynomial using divVar
  -- maybe work the algebra out for this first and test the method
  -- the process is like, Z f(x) = CZ x_i f'(x')
  -- where f(x) is some polynomial in the form  x_i * f'(x') where x' does not contain x_i
  -- so we are using divVar to find that polynomial, by a recursive factoring process
  -- and then we will additionally be recursing to deal with every x_i in turn
  -- so it sounds a bit like the shaving
  let xagDagGates = reverse xagGates -- TODO REMOVE
  --
  let rzGates = xagGates ++ phaseGates ++ xagDagGates
  emitGates sop rzGates
  where
    factorize p = Set.foldr tryDiv ([], p) $ vars p
      where tryDiv x  (acc, poly) =
              let (q, r) = divVar poly x in
                if isZero r then ((ofVar x):acc, q) else (acc, poly)

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
               tell [MCT controls target]
               return $ sop { outVals = addTermAt term i (outVals sop) }
  addTermAt term i xs =
    let (head, y:ys) = splitAt i xs in
      head ++ (y + ofTerm term):ys

-- | Assuming the ket is in the form |A(x1...xn) + b>, synthesizes
--   the transformation |x1...xn> -> |A(x1...xn) + b>
finalize :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalize sop
  | isIdentity (dropPhase (grind sop)) = return sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_AffineSynth = finalizeAffineSynth sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_MCTSynth = finalizeMCTSynth sop
  | ctlEnabled fcfFeature_Synthesis_Pathsum_Unitary_XAGSynth = finalizeXAGSynth sop

finalizeAffineSynth :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalizeAffineSynth sop = do
  ctx <- gets idToIndex
  let input = Map.map (\i -> (bitI n i, False)) ctx
  let output = Map.map (\i -> bitvecOfPoly $ (outVals sop)!!i) ctx
  let circ = dagger $ affineSynth input output
  let gates = map toMCT circ
  tell gates
  applyExtract sop gates
  where n = inDeg sop
        bitvecOfPoly p = (foldr xor (bitI 0 0) . map bitvecOfVar . Set.toList $ vars p, getConstant p == 1)
        bitvecOfVar (IVar i) = bitI n i
        bitvecOfVar (PVar _) = error "Attempting to finalize a proper path-sum!"
        bitvecOfVar (FVar _) = error "Attempting to extract a path-sum with free variables!"

finalizeMCTSynth :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalizeMCTSynth sop = do
  traceU ("finalizeMCTSynth " ++ show sop) $ return ()
  prefix <- freshPrefix
  -- ancID generates an ancilla ID to match a particular qubit ID
  let ancID qID = prefix ++ "M" ++ qID
  revCtx <- gets indexToID
  let qIDs = Map.elems revCtx
  let n = outDeg sop
  traceU ("  prefix: " ++ prefix) $ return ()
  let sopClassical = dropPhase sop
  let invopClassical = grind (PS.dagger sopClassical)
  -- assumes ids in ctx are [0..n-1], with no gaps
  let idSBools = zip qIDs (map (rename (\(IVar i) -> revCtx ! i)) (outVals sopClassical))
  let invIDSBools = zip qIDs (map (rename (\(IVar i) -> revCtx ! i)) (outVals invopClassical))
  traceU ("  idSBools: " ++ show idSBools) $ return ()
  traceU ("  invIDSBools: " ++ show invIDSBools) $ return ()
  -- termMCTs gives the MCT computing one term (with inversion if needed)
  let termMCTs target val termIDs
        | val == 0 = [MCT termIDs target, MCT [] target]
        | otherwise = [MCT termIDs target]
  -- sboolMCTs gives a list of MCTs computing a particular SBool
  let sboolMCTs targetID sbool =
        concat [termMCTs targetID val (Set.toList (vars term))
                | (val, term) <- toTermList sbool]
  -- Compute the desired function, with the fresh ancillas as target
  -- (reverse it because we generally are tell'ing the dagger of the circuit;
  -- note for this implementation computing into fresh ancillas is Hermitian,
  -- so self-inverse, therefore this is aesthetic more than functional)
  let gates = reverse (concatMap (\(qID, sbool) -> sboolMCTs (ancID qID) sbool) idSBools)
  -- Uncompute the inverse of the desired function
  let invGates = concatMap (\(qID, sbool) -> sboolMCTs (ancID qID) sbool) invIDSBools
  -- After the uncomputation of the inverse, the desired output needs to be in
  -- the ancillas, and the inputs |0>'s, so we start by swapping everything
  -- into place
  emitGates sop (invGates ++ [Swapper (ancID qID) qID | (qID, _) <- idSBools] ++ gates)

finalizeXAGSynth :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
finalizeXAGSynth sop = do
  traceU ("finalizeXAGSynth " ++ show sop) $ return ()
  prefix <- freshPrefix
  revCtx <- gets indexToID
  let qIDs = Map.elems revCtx
  let n = outDeg sop
  traceU ("  prefix: " ++ prefix) $ return ()
  let sopClassical = dropPhase sop
  let invopClassical = grind (PS.dagger sopClassical)

  let fwdXAG = minimizeXAG (fromSBools n (outVals sopClassical))
  let revXAG = minimizeXAG (fromSBools n (outVals invopClassical))
  let (xagGates, _) = inputErasingXAGSynth fwdXAG revXAG qIDs [prefix ++ show i | i <- [1..]]
  -- reverse, because we generally are tell'ing the dagger of the circuit
  emitGates sop (reverse xagGates)

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

-- | Synthesize a multiply-controlled Toffoli gate
synthesizeMCT :: Int -> [ID] -> ID -> [Primitive]
synthesizeMCT _ [] t       = [X t]
synthesizeMCT _ [x] t      = [CNOT x t]
synthesizeMCT _ [x,y] t    = ccx x y t
synthesizeMCT i (x:xs) t   = circ ++ ccx x ("_anc" ++ show i) t ++ circ where
  circ = synthesizeMCT (i+1) xs ("_anc" ++ show i)

-- | Push swaps to the end
pushSwaps :: [ExtractionGates] -> [ExtractionGates]
pushSwaps = reverse . go (Map.empty, []) where
  -- Convenience; we want the empty ctx map to map everything to itself
  get :: Map ID ID -> ID -> ID
  get ctx q               = Map.findWithDefault q q ctx
  synthesize :: (Map ID ID, [ExtractionGates]) -> [ExtractionGates]
  -- Beware, the final synthesis of swaps is a bit subtle. The ctx map
  -- expresses a permutation, and we decompose it into a series of orbits aka
  -- cycles. When emitting the Swapper gates for each orbit, the order of the
  -- swaps is important, because it determines which way around the orbit the
  -- elements are cycling. If you reverse the order of two swaps, those
  -- elements will cycle in the opposite direction from the others, and you
  -- won't get the orbit you wanted.
  synthesize (ctx, acc) =
    case Map.toList ctx of
      [] -> acc
      (q, q'):_ -> synthesize (synthesizeOrbit q' (Map.delete q ctx, acc))
  synthesizeOrbit :: ID -> (Map ID ID, [ExtractionGates]) -> (Map ID ID, [ExtractionGates])
  -- Since we're deleting elements as we go, failure to find the next element
  -- in the chain indicates we've come back to the start and are done.
  synthesizeOrbit q (ctx, acc) =
      case ctx Map.!? q of
        Just q' -> synthesizeOrbit q' (Map.delete q ctx, (Swapper q q'):acc)
        Nothing -> (ctx, acc)
  -- This algorithm operates in two phases: first it walks through the list of
  -- gates, building up a mapping as it goes (which is really just the overall
  -- permutation the sequence of swaps represents). At the same time it removes
  -- any Swapper (using the args to update the mapping), and rewrites the qubit
  -- references in the circuit. That leaves you with an equivalent circuit,
  -- modulo swaps. The second phase is implemented by "synthesize" above: it
  -- emits a sequence of swaps to make the equivalence exact.
  go :: (Map ID ID, [ExtractionGates]) -> [ExtractionGates] -> [ExtractionGates]
  go (ctx, acc) []        = synthesize (ctx, acc)
  go (ctx, acc) (x:xs)    = case x of
    -- Hadamard, Phase, MCT get rewritten using the mapping
    Hadamard q    -> go (ctx, (Hadamard $ get ctx q):acc) xs
    Phase a cs    -> go (ctx, (Phase a $ map (get ctx) cs):acc) xs
    MCT cs t      -> go (ctx, (MCT (map (get ctx) cs) (get ctx t)):acc) xs
    -- Swapper is removed, and causes an update of the mapping
    Swapper q1 q2 ->
      let (q1', q2') = (get ctx q1, get ctx q2) in
        go (Map.insert q1 q2' $ Map.insert q2 q1' ctx, acc) xs

{-----------------------------------
 Extraction
 -----------------------------------}

{-
-- | A single pass of the synthesis algorithm
synthesizeFrontier :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizeFrontier sop = go (grind sop) where
  go sop
    | pathVars sop == 0 = synthesisPass sop >>= finalize
    | otherwise         = synthesisPass sop >>= reducePaths
  synthesisPass = affineSimplifications >=>
                  phaseSimplifications >=>
                  nonlinearSimplifications >=>
                  phaseSimplifications
  reducePaths sop = do
    sop' <- hLayer sop >>= normalize
    case pathVars sop' < pathVars sop of
      True  -> return sop'
      False -> strengthReduction sop' >>= synthesisPass >>= hLayer >>= normalize
--}

--{-
-- | A single pass of the synthesis algorithm
synthesizeFrontier :: (HasFeynmanControl) => Pathsum DMod2 -> ExtractionState (Pathsum DMod2)
synthesizeFrontier sop =
  traceU ("Synthesizing " ++ show sop) $
    go (grind sop)
  where
    go sop
      | pathVars sop == 0 = do
        traceU ("finalizing, before synthesisPass: " ++ show sop) $ return ()
        sop' <- synthesisPass sop
        traceU ("finalizing, after synthesisPass: " ++ show sop') $ return ()
        finalize sop'
      | otherwise = do
        traceU ("reducing, before synthesisPass: " ++ show sop) $ return ()
        sop' <- synthesisPass sop
        traceU ("reducing, after synthesisPass: " ++ show sop') $ return ()
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
--}

-- | Extract a Unitary path sum. Returns Nothing if unsuccessful
extractUnitary :: (HasFeynmanControl) => Ctx -> Pathsum DMod2 -> Maybe [ExtractionGates]
extractUnitary ctx sop = processWriter $ evalStateT (go sop) ctx where
  processWriter w = case runWriter w of
    (True, circ) -> Just $ daggerDep circ
    _            -> Nothing
  go sop = do
    sop' <- synthesizeFrontier sop
    if pathVars sop' < pathVars sop
      then go sop'
      else return $ isTrivial sop'

-- | Resynthesizes a circuit
resynthesizeCircuit :: (HasFeynmanControl) => [Primitive] -> Maybe [ExtractionGates]
resynthesizeCircuit xs = liftM pushSwaps $ extractUnitary (mkctx ctx) sop where
  (sop, ctx) = runState (computeAction xs) Map.empty
