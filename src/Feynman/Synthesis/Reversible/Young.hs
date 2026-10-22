module Feynman.Synthesis.Reversible.Young where

import Control.Exception (assert)
import Debug.Trace qualified

import Data.Array.Unboxed qualified as Array
import Data.Array.IArray qualified as Array
import Data.Array.IArray (Array)
import Data.Bifunctor (bimap)
import Data.Bits ((.|.), shiftL)
import Data.BitVector qualified as BitVector
import Data.Foldable (foldl')
import Data.IntMap qualified as IntMap
import Data.IntMap (IntMap)
import Data.IntSet qualified as IntSet
import Data.IntSet (IntSet)
import Data.List (partition, zip4, unzip3)
import Data.Map.Strict qualified as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromJust, listToMaybe)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.IntSet qualified as IntSet
import Data.IntSet (IntSet)

import Feynman.Control
import Feynman.Core hiding (subst)

import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced (Var (..))
import Feynman.Algebra.Polynomial hiding (Var)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Synthesis.Pathsum.Util

type Term = PowerProduct Var
type Func = SBool Var

type SolveHiMethod = Var -> Func -> [Var] -> [(Var, Func)] -> Maybe (Func, Func)


traceY :: (HasFeynmanControl) => String -> a -> a
traceY msg val
  | ctlEnabled fcfTrace_Synthesis_Reversible_Young = Debug.Trace.trace msg val
  | otherwise = val


-- take a boolean function and synthesize input-erasing
-- returns ExtractionGates
youngDecompositionSynth :: (HasFeynmanControl) => (Var -> Func -> [Var] -> [(Var, Func)] -> Maybe (Func, Func)) -> [(ID, Var, Func)] -> Maybe [ExtractionGates]
youngDecompositionSynth solveHi idXiSbools = do
  decomposedFuncs <-
    -- all vars in all terms in all SBools must be IVar i, i >= 0
    assert (all (\v -> case v of IVar i -> i >= 0; otherwise -> False) xiVars) $
    decomposeAll solveHi (zip4 xiVars fiVars siVars sbools)
  extractCircuit [(xi, gi, hi) | (xi, (gi, hi)) <- zip xiVars decomposedFuncs]
  where
    (idsList, xiVars, sbools) = unzip3 idXiSbools
    n = length sbools
    k = foldl' max 0 [i | (IVar i) <- xiVars]
    fiVars = [IVar ((max k 100) + i) | i <- [1 .. n]]
    siVars = [IVar ((max (k + n) 200) + i) | i <- [1 .. n]]
    varToID = Map.fromList (zip xiVars idsList ++ zip fiVars idsList ++ zip siVars idsList)

    extractCircuit :: [(Var, Func, Func)] -> Maybe [ExtractionGates]
    extractCircuit [] = Just []
    extractCircuit ((xi, gi, hi) : remain) = do
      giCirc <- extractFunc gi xi
      remainCirc <- extractCircuit remain
      hiCirc <- extractFunc hi xi
      Just (giCirc ++ remainCirc ++ hiCirc)

    extractFunc :: Func -> Var -> Maybe [ExtractionGates]
    extractFunc f target = do
      targetID <- Map.lookup target varToID
      -- Check that the term coefficients are all 1
      _ <- if all (== 1) (map fst (toTermList f)) then Just () else (traceY ("Term(s) with coefficient /= 1 in " ++ show target ++ " = " ++ show f) $ Nothing)
      let allTermVars = map (Set.toList . vars) (map snd (toTermList f))
      allTermIDs <- mapM (mapM (flip Map.lookup varToID)) allTermVars
      _ <- if all (/= targetID) (concat allTermIDs) then Just () else (traceY ("targetID " ++ targetID ++ " in mapped terms of " ++ show target ++ " = " ++ show f) $ Nothing)
      Just [MCT termIDs targetID | termIDs <- allTermIDs]


decomposeAll :: (HasFeynmanControl) => SolveHiMethod -> [(Var, Var, Var, Func)] -> Maybe [(Func, Func)]
decomposeAll solveHi funcs = decomposeRemain funcs [] >>= (Just . reverse)
  where
    decomposeRemain :: [(Var, Var, Var, Func)] -> [(Var, Func, Func)] -> Maybe [(Func, Func)]
    decomposeRemain [] soFar = Just [(gi, hi) | (_, gi, hi) <- soFar]
    decomposeRemain ((xiVar, fiVar, siVar, fiFunc):remain) soFar = do
      (hi, hiSubst) <- solveHi xiVar fiFunc sjVars fjFuncs
      -- hiSubst should be written in the same variables as the desired g_i
      let gi = fiFunc + hiSubst + ofVar xiVar
      decomposeRemain (substRemain gi) ((siVar, gi, hi) : soFar)
      where
        sjVars = [sjVar | (sjVar, _, _) <- soFar]
        fjFuncs = [(fjVar, fjFunc) | (_, fjVar, _, fjFunc) <- remain]

        -- Rewrite the remaining f_j polynomials in terms of s_i, so that x_i
        -- doesn't appear in them anymore. This is fairly trivial only because
        -- x_i by definition doesn't appear in g_i, and we have defined
        -- s_i = x_i + g_i, therefore x_i = g_i + s_i.
        -- Doing this incrementally as we recurse leaves us in the happy
        -- position that we are working in a space where the f_i is written in
        -- the same variables as g_i, making g_i trivial to find once we have
        -- h_i (this is important in decomposeOne below -- well, more
        -- specifically it's going to give us something technically correct
        -- anyway, but if we're trying to synthesize logic and we have
        -- computed a bunch of qubits to s_j already, it's nice if the g_i
        -- we're synthesizing is written exactly in terms of what we have to
        -- hand; it saves us doing inversions).
        substRemain gi = [(xjVar, fjVar, sjVar, subst xiVar (gi + ofVar siVar) fjFunc)
                          | (xjVar, fjVar, sjVar, fjFunc) <- remain]


-- With f(x) a reversible function from F_2^n -> F_2^n, decompose f_i(x) into
--   x_i + g_i(p_i) + h_i(q_i) = f_i(x)
--   where:
--     s_i = x_i + g_i(p_i),
--     p_i = (s_1, .., s_i-1, x_i+1, .., x_n),
--     q_i = (s_1, .., s_i-1, f_i+1, .., f_n).
-- Takes: the f_i we are decomposing and its input x_i; the s_j's, j < i; and
--        f_j's vars and polynomials in x, j > i
-- Returns: if found, Just (h_i(q_i), h_i(p_i)); otherwise Nothing
solveHiByGaussianElimination :: (HasFeynmanControl) => Var -> Func -> [Var] -> [(Var, Func)] -> Maybe (Func, Func)
solveHiByGaussianElimination xiVar fiFunc sjVars fjFuncs =
  traceY ("solveHiByGaussianElimination") $
  traceY ("  fjFuncs: " ++ show fjFuncs) $
  traceY ("  idxMap: " ++ show idxMap) $
  traceY ("  varMap: " ++ show varMap) $
  if any ((/= 1) . fst) (toTermList fiFunc) then error ("Bad coefficient (not 1) in " ++ show fiFunc) else
    traceY ("  fiFunc: " ++ show fiFunc) $
    traceY ("  support fiFunc: " ++ show (support fiFunc)) $
    traceY ("  fiPoly: " ++ show fiPoly) $
    traceY ("  trivialBasis: " ++ show trivialBasis) $
    solveHiWithBasis genBasis (polynomialBits (ofVar xiVar + fiFunc), 0)
  where
    trivialVarSet = Set.fromList (xiVar : sjVars)
    allVars = Set.toList (foldl' Set.union trivialVarSet [vars f | (_, f) <- fjFuncs])
    allVarIs = [vi | (IVar vi) <- allVars]
    n = length allVarIs

    varMap = IntMap.fromAscList (zip allVarIs [0..])
    idxMap = Array.array (0, n - 1) (zip [0..] allVarIs) :: Array.UArray Int Int

    zeroBits = BitVector.bitVec n 0
    varBits (IVar vi) = (BitVector.bitVec n 1) `shiftL` (varMap IntMap.! vi)
    monomialBits m = foldl' (.|.) zeroBits [varBits v | v <- Set.toList (getVars m)]

    polynomialBits p = Set.fromList [monomialBits m | m <- support p]

    addVarBits :: Set BitVector.BV -> BitVector.BV -> Set BitVector.BV
    addVarBits p v = fromJust (Set.alterF (Just . not) v p)
    addPolyBits :: Set BitVector.BV -> Set BitVector.BV -> Set BitVector.BV
    addPolyBits = Set.symmetricDifference
    multPolyBits :: Set BitVector.BV -> Set BitVector.BV -> Set BitVector.BV
    multPolyBits x y = foldl' addVarBits Set.empty
                              [xi .|. yj | xi <- Set.toList x, yj <- Set.toList y]
    
    reduce :: Basis -> Set BitVector.BV -> Func -> (BitVector.BV, (Set BitVector.BV, Func))
    reduce basis gSide hSide
      | traceY ("  reduce: " ++ show gSide ++ " <-> " ++ show hSide) $ False = undefined
      -- No terms, gSide is completely reduced to 0
      | Set.null gSide = traceY ("    fully reduced (is 0)") $ (zeroBits, (gSide, hSide))
      | otherwise =
        -- Is there a pivot for the leading term?
        case basis Map.!? leadBits of
          -- Yes, use it to cancel and then continue reduction
          Just (polyBits, func) -> reduce basis (addPolyBits gSide polyBits) (hSide + func)
          -- Pivot not found, we are irreducible
          Nothing -> traceY ("    irreducible") $ (leadBits, (gSide, hSide))
      where
        leadBits = Set.elemAt 0 gSide

    addToBasis :: Basis -> (Set BitVector.BV, Func) -> (Basis)
    addToBasis basis (gSidePoly, hSideFunc) =
      if Set.null reducedGSide then basis else (Map.insert leadBits (reducedGSide, reducedHSide) basis)
      where
        (leadBits, (reducedGSide, reducedHSide)) = reduce basis gSidePoly hSideFunc

    fiPoly = polynomialBits fiFunc

    trivialBasis :: Map BitVector.BV (Set BitVector.BV, Func)
    trivialBasis = Map.fromList ((zeroBits, (Set.singleton zeroBits, 1))
                                   : [(varBits v, (Set.singleton (varBits v), ofVar v))
                                     | v <- sjVars])
    genBasis = foldl' addToBasis trivialBasis [(polynomialBits fjFunc, ofVar fjVar)
                                              | (fjVar, fjFunc) <- fjFuncs]

    productBasis bx by =
      foldl' addToBasis bx [(multPolyBits xBits yBits, xFunc * yFunc)
                           | (xBits, xFunc) <- Map.elems bx, (yBits, yFunc) <- Map.elems by]

    solveHiWithBasis basis (gSide, hSide)
      | traceY ("  solve - basis: " ++ show basis) $
        traceY ("          gSide: " ++ show gSide) $
        traceY ("          hSide: " ++ show hSide) $
        False = undefined

      -- done?
      | null reducedGSide = Just (0, reducedHSide)
      -- basis no longer expanding? Solution is impossible
      | expandedBasis == basis = Nothing
      -- recurse
      | otherwise = solveHiWithBasis expandedBasis (reducedGSide, reducedHSide)
      where
        expandedBasis = (productBasis basis genBasis)
        (leadBits, (reducedGSide, reducedHSide)) = reduce basis gSide hSide
        
type Basis = Map BitVector.BV (Set BitVector.BV, Func)


-- With f(x) a reversible function from F_2^n -> F_2^n, decompose f_i(x) into
--   x_i + g_i(p_i) + h_i(q_i) = f_i(x)
--   where:
--     s_i = x_i + g_i(p_i),
--     p_i = (s_1, .., s_i-1, x_i+1, .., x_n),
--     q_i = (s_1, .., s_i-1, f_i+1, .., f_n).
-- Takes: the f_i we are decomposing and its input x_i; the s_j's, j < i; and
--        f_j's vars and polynomials in x, j > i
-- Returns: if found, Just (h_i(q_i), h_i(p_i)); otherwise Nothing
solveHiByEnumeration :: (HasFeynmanControl) => Var -> Func -> [Var] -> [(Var, Func)] -> Maybe (Func, Func)
solveHiByEnumeration xiVar fiFunc sjVars fjFuncs =
  -- h_i should be written using s_j's, f_j's
  listToMaybe (filter (differsOnlyByTrivial nontrivialFiTerms . snd)
                      [ {-- traceY ("considering f(s) = " ++ show fs) $ --} (fs, fx)
                        | (fs, fx) <- nonTrivialHiCandidates])
    >>= (\(nonTrivialHiPart, nonTrivialHiSubstPart) ->
            Just (nonTrivialHiPart + trivialFiTerms, nonTrivialHiSubstPart + trivialFiTerms))
  where
    xiFunc = ofVar xiVar

    trivialVars :: Term
    trivialVars = monomial sjVars
    isTrivialHiTerm :: (a, Term) -> Bool
    isTrivialHiTerm (_, vs) = Set.null (getVars (vs ./. trivialVars))
    nontrivialHiTerms hF = ofTermList (filter (not . isTrivialHiTerm) (toTermList hF))
    differsOnlyByTrivial hA hB =
      traceY ("differs? nt hA = " ++ (show (nontrivialHiTerms hA)) ++ "; nt hB = "
                                 ++ (show (nontrivialHiTerms hB)) ++ "; hA + hB = "
                                 ++ (show (nontrivialHiTerms hA + nontrivialHiTerms hB))) $
      isZero (nontrivialHiTerms hA + nontrivialHiTerms hB)

    -- The "trivial" part of the function we're constructing is the terms of
    -- g_i + h_i (or equivalently f + x_i), where the terms only contain s_j
    -- as variables (where j > i). Those are trivial because we can just
    -- return them directly, they're not substituted.
    -- "Nontrivial" is everything else in the function we're constructing,
    -- that is, the terms of g_i + h_i (or equivalently f + x_i), where the
    -- terms contain at least one variable not in s_j (where j > i).
    (trivialFiTerms, nontrivialFiTerms) =
      bimap ofTermList ofTermList . partition isTrivialHiTerm
                                     . toTermList $ xiFunc + fiFunc

    relevantFjFuncs = fjFuncs
    relevantSjVars = filter (`Set.member` (Set.fromList sjVars)) (Set.toList (vars fiFunc))

    nonTrivialHiCandidates = allFuncsFromSubst (relevantFjFuncs ++ [(v, ofVar v) | v <- relevantSjVars])

-- traceAllY [] result                = result
-- traceAllY (msg : msgRemain) result = traceY msg $ traceAllY msgRemain result


allFuncsFromSubst :: (HasFeynmanControl) => [(Var, Func)] -> [(Func, Func)]
allFuncsFromSubst substList =
  funcsByOrder substVars
  where
    substVars = fst . unzip $ substList
    substMap = Map.fromList substList

    funcsByOrder :: [Var] -> [(Func, Func)]
    funcsByOrder termVars =
      [(ofTermList [(1, t) | t <- ts], tf) | (ts, tf) <- allSelections allTermFuncsOrdered]
      where
        allSelections :: [(Term, Func)] -> [([Term], Func)]
        allSelections termFuncs = nextSelectionsGen [([], zero)] termFuncs
          where
            nextSelectionsGen lastGen [] = lastGen
            nextSelectionsGen lastGen ((t, f) : remain) = nextSelectionsGen thisGen remain
              where thisGen = lastGen ++ [(t : lt, lf + f) | (lt, lf) <- lastGen]

        allTermFuncsOrdered :: [(Term, Func)]
        allTermFuncsOrdered = [(t, substitutedTermFunc t) | t <- allTermsOrdered]
          where
            -- substitute all the vars in the term using substMap, which rewrites f_j vars to x_j vars
            substitutedTermFunc :: Term -> Func
            substitutedTermFunc t = product [Map.findWithDefault (ofVar v) v substMap | v <- Set.toList (vars t)]

            -- This might be made a fair bit faster by denormalizing the last
            -- iteration level: catch the "unused termVars 1" case and instead of
            -- bottoming out every recursion individually, map `monomial` over
            -- `unused` to combine each one with `termVars`.
            -- Also need to check whether the current structure makes effective use of
            -- lazy eval, I seem to recall reading that (++) causes issues.
            termsOfOrder :: [Var] -> [Var] -> Int -> [Term]
            termsOfOrder _ termVars 0 = [monomial termVars]
            termsOfOrder [] _ _ = []
            termsOfOrder unusedVars _ n | length unusedVars < n = []
            termsOfOrder (v : unusedVarsRemain) termVars n =
              termsOfOrder unusedVarsRemain (v : termVars) (n - 1)
                ++ termsOfOrder unusedVarsRemain termVars n

            allTermsOrdered :: [Term]
            allTermsOrdered = concat [termsOfOrder termVars [] n | n <- [0 .. length termVars]]

