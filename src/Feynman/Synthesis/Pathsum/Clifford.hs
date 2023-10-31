{-# LANGUAGE TupleSections #-}

{-|
Module      : Clifford
Description : Extraction of Clifford path sums to circuits
Copyright   : (c) Matthew Amy, 2021
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Synthesis.Pathsum.Clifford(
  isClifford,
  isUnitary,
  extractClifford,
  resynthesizeClifford,
  generateClifford
  ) where

import Data.Semigroup ((<>))
import Data.Maybe (mapMaybe, fromMaybe, fromJust, maybe)
import Data.List ((\\))
import Data.Map (Map, (!))
import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad (foldM, mapM, mfilter)
import Control.Monad.Writer.Lazy (Writer, tell, runWriter)
import Control.Monad.State.Strict (runState)

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

import Feynman.Core (ID, Primitive(..), Angle(..))
import Feynman.Algebra.Base
import Feynman.Algebra.Linear (bitI)
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced

import Feynman.Synthesis.Phase
import Feynman.Synthesis.Reversible

import Feynman.Verification.Symbolic

{-----------------------------------
 Extractability checks
 -----------------------------------}

-- | Checks whether a path sum is Clifford (c.f. stabilizer)
isClifford :: Pathsum DMod2 -> Bool
isClifford sop = ord (phasePoly sop) <= 2 && all ((1 >=) . degree) (outVals sop)
  where ord p | p == 0    = 0
              | otherwise = maximum . map ordTerm . toTermList $ p
        ordTerm (a,m)     = fromInteger (denom $ unpack a) + (degree m) - 1

-- | Checks whether a Clifford path sum is unitary
isUnitary :: (Eq g, Periodic g, Dyadic g) => Pathsum g -> Bool
isUnitary sop
  | inDeg sop /= outDeg sop = False
  | otherwise               = isTrivial (normalizeClifford $ sop .> dagger sop) &&
                              isTrivial (normalizeClifford $ dagger sop .> sop)

{-----------------------------------
 Utilities
 -----------------------------------}

-- | ID for the ith variable
var :: Int -> ID
var = ("q" ++) . show

-- | The number of an ID
unvar :: ID -> Int
unvar = read . tail

-- | Normalizes the outputs of a path sum, up to Cliffords
normalizeOutputs :: Pathsum DMod2 -> Writer [Primitive] (Pathsum DMod2)
normalizeOutputs sop = go sop 0 where
  go sop i
    | i >= outDeg sop = return sop
    | otherwise       = case filter (\(v,p) -> isP v && p /= 0) . solveForX $ (outVals sop)!!i of
      []      -> go sop (i+1)
      (v,p):_ -> do
        let sop' = applyVar v (p + ofVar v) sop
        outVals' <- mapM (removeVar i v) $ zip (outVals sop') [0..]
        go (grind $ sop' { outVals = outVals' }) 0
  removeVar i v (f, j)
    | i >= j || not (Set.member v (vars f)) = return f
    | otherwise                             = do
      tell [CNOT (var i) (var j)]
      return (f + ofVar v)

-- | Internal normalization up to Cliffords
normalizeInternal :: Pathsum DMod2 -> Writer [Primitive] (Pathsum DMod2)
normalizeInternal sop = foldM go (normalizeClifford sop) [0..outDeg sop - 1] where
  go sop i = case filter (\(v,p) -> isP v && p == 0) . solveForX $ (outVals sop)!!i of
    []      -> return sop
    (v,_):_ -> do
      outVals' <- mapM (removeVar i v) $ zip (outVals sop) [0..]
      return $ sop { outVals = outVals' }
  removeVar i v (f, j)
    | i == j || not (Set.member v (vars f)) = return f
    | otherwise                             = do
      tell [CNOT (var i) (var j)]
      return (f + ofVar v)

-- | Renames the normalized outputs in ascending order
renameOutputs :: Pathsum DMod2 -> Pathsum DMod2
renameOutputs sop = sop { phasePoly = rename sub (phasePoly sop),
                          outVals   = map (rename sub) (outVals sop) }
  where pvars  = filter isP . mapMaybe asVar . outVals $ sop
        varMap = Map.fromList . flip zip (map PVar [0..]) $ pvars
        sub v  = fromMaybe v $ Map.lookup v varMap

{-----------------------------------
 Extraction
 -----------------------------------}

-- | Extract a Clifford path sum. Returns Nothing if unsuccessful
--
--   If successful, produces a circuit of the form S CZ CX H S CZ CX. The
--   algorithm proceeds as follows:
--     1. remove all internal path variables via [Elim] [HH] and [\(\omega\)]
--     2. rewrite output so that the ith qubit is either \(y_i\) or \(Q_i(\vec{x})\)
--        2.1. for each i, check if the ith qubit is \(y_j + g(\vec{x})\)
--             2.1.1 substitute \(y_j\) with \(y_j + g(\vec{x})\)
--             2.1.2 remove \(y_j\) from all other outputs
--        2.2. rename remaining variables
--     3. let \(P(\vec{x},\vec{y}) = A(\vec{x}) + B(\vec{y}) + \sum_i y_iQ_i(\vec{x},\vec{y})\)
--     4. synthesize \(|\vec{x}\rangle \mapsto i^{A(\vec{x})}|\vec{x}\rangle\)
--     5. synthesize \(|\vec{x}\rangle \mapsto |\vec{Q(\vec{x}}\rangle\)
--     6. apply \(H\) gates wherever the ith qubit is \(y_i\)
--     7. synthesize \(|\vec{y}\rangle \mapsto i^{B(\vec{y})}|\vec{y}\rangle\)
extractClifford :: Pathsum DMod2 -> Maybe [Primitive]
extractClifford sop = validated >>= return . extract where
  validated   = Just sop --if isClifford sop && isUnitary sop then Just sop else Nothing
  extract sop =
    let (sop', c5) = runWriter . normalizeInternal $ sop
        pMap = filter (isP . fst) . mapMaybe (\(p,i) -> fmap (,i) $ asVar p) . zip (outVals sop') $ [0..]
        a = collectBy (all isI . vars . snd) $ phasePoly sop'
        b = collectBy (all isP . vars . snd) $ phasePoly sop' - a
        c = phasePoly sop' - a - b
        f = map qi (outVals sop') where
          qi p = maybe p (fromJust . toBooleanPoly . (flip quotVar) c) . mfilter isP $ asVar p
        c1 = synthesizePP . renameMonotonic (\(IVar i) -> var i) $ a
        c2 = synthesizeAffine . map (renameMonotonic (\(IVar i) -> var i)) $ f
        c3 = map (H . var . snd) pMap
        c4 = synthesizePP . renameMonotonic (var . ((Map.fromList pMap)!)) $ b
    in
      c1 ++ c2 ++ c3 ++ c4 ++ (reverse c5)

-- | Synthesize a Clifford phase polynomial. Unsafe
synthesizePP :: PseudoBoolean ID DMod2 -> [Primitive]
synthesizePP poly = concatMap synthesizeTerm . map expandMonomial . toTermList $ poly where
  expandMonomial (a,m)       = (a, Set.toList $ vars m)
  synthesizeTerm (a,[])      = globalPhase (var 0) (Discrete a)
  synthesizeTerm (a,[v])     = synthesizePhase v (Discrete a)
  synthesizeTerm (1,[v1,v2]) = [CZ v1 v2]

-- | Synthesize an affine transformation. Unsafe
synthesizeAffine :: [SBool ID] -> [Primitive]
synthesizeAffine f = affineSynth input output where
  input     = Map.fromList $ [(var i, (bitI (length f) i, False)) | i <- [0..length f - 1]]
  output    = Map.fromList . map (\(i, fi) -> (var i, (toVec fi, constTerm fi))) $ zip [0..] f
  toVec     = sum . map (bitI (length f) . unvar) . Set.toList . vars
  constTerm = (== 1) . getConstant

-- | Re-synthesize a Clifford circuit. Raises an error if unsuccessful.
--   TODO: this does the simple ugly thing of using the computed context to apply a final
--   substitution on the circuit. It should really be threading a context through the
--   extraction method
resynthesizeClifford :: [Primitive] -> [Primitive]
resynthesizeClifford xs = case extractClifford sop of
  Nothing  -> error $ "Could not extract path sum:\n  " ++ show sop
  Just xs' -> Core.subst sub xs'
  where (sop, ctx) = runState (computeAction xs) Map.empty
        qubits     = Map.fromList . map (\(a,b) -> (b,a)) . Map.toList $ ctx
        sub        = (qubits!) . unvar


-- | Clifford basis
xGate :: Pathsum DMod2
xGate = xgate

zGate :: Pathsum DMod2
zGate = zgate

sGate :: Pathsum DMod2
sGate = sgate

hGate :: Pathsum DMod2
hGate = hgate

cxGate :: Pathsum DMod2
cxGate = cxgate

-- | More challenging circuits
test1 = (hGate <> hGate) .> cxGate .> (hGate <> hGate)
test2 = (hGate <> identity 1) .> cxGate .> (hGate <> identity 1)
test3 = (identity 1 <> hGate) .> cxGate .> (identity 1 <> hGate)

{-----------------------------------
 Automated tests
 -----------------------------------}

-- | Maximum size of circuits
maxSize :: Int
maxSize = 9

-- | Maximum length of circuits
maxGates :: Int
maxGates = 100

-- | Type for generating instances of Clifford circuits
newtype Clifford = Clifford [Primitive] deriving (Show, Eq)

instance Arbitrary Clifford where
  arbitrary = fmap Clifford $ resize maxGates $ listOf $ oneof gates where
    gates = [genH maxSize, genS maxSize, genCX maxSize]

-- | Random CX gate
genCX :: Int -> Gen Primitive
genCX n = do
  x <- chooseInt (0, n)
  y <- chooseInt (0, n) `suchThat` (/= x)
  return $ CNOT (var x) (var y)

-- | Random S gate
genS :: Int -> Gen Primitive
genS n = do
  x <- chooseInt (0,n)
  return $ S (var x)

-- | Random H gate
genH :: Int -> Gen Primitive
genH n = do
  x <- chooseInt (0,n)
  return $ H (var x)

-- | Checks that the path sum of a Clifford circuit is indeed Clifford
prop_Clifford_is_Clifford :: Clifford -> Bool
prop_Clifford_is_Clifford (Clifford xs) = isClifford $ simpleAction xs

-- | Checks that the path sum of a Clifford circuit is indeed Unitary
prop_Clifford_is_Unitary :: Clifford -> Bool
prop_Clifford_is_Unitary (Clifford xs) = isUnitary $ simpleAction xs

-- | Checks that the path sum of a Clifford circuit is correctly extracted
prop_Clifford_Extraction_Correct :: Clifford -> Bool
prop_Clifford_Extraction_Correct (Clifford xs) = go where
  go  = isTrivial . normalizeClifford . simpleAction $ xs ++ Core.dagger xs'
  xs' = resynthesizeClifford xs

-- | Generates a random Clifford circuit
generateClifford :: Int -> Int -> IO [Primitive]
generateClifford n k = generate customArbitrary where
  customArbitrary = resize k $ listOf1 $ oneof [genH n, genS n, genCX n]
