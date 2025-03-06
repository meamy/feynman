module Specs.SynthesisPathsumUnitarySpec where

import Control.Monad
import Control.Monad.Writer.Lazy
import Control.Monad.State.Strict
import Data.Map (Map, (!))
import Data.Maybe
import qualified Data.Map as Map
import Test.Hspec

--import qualified Feynman.Core as Core
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced
import qualified Feynman.Algebra.Pathsum.Balanced as PS
import Feynman.Circuits
import Feynman.Core
import Feynman.Synthesis.Pathsum.Clifford
import Feynman.Synthesis.Pathsum.Unitary
import Feynman.Synthesis.Pathsum.Util
import Feynman.Verification.Symbolic

import Arbitrary.CliffordT

-- | Primitive to MCT gate
toExtraction :: Primitive -> ExtractionGates
toExtraction g = case g of
  CNOT c t -> MCT [c] t
  X t      -> MCT []  t
  Swap x y -> Swapper x y
  H t      -> Hadamard t
  Z t      -> Phase (fromDyadic $ dyadic 1 0) [t]
  S t      -> Phase (fromDyadic $ dyadic 1 1) [t]
  Sinv t   -> Phase (fromDyadic $ dyadic 3 1) [t]
  T t      -> Phase (fromDyadic $ dyadic 1 2) [t]
  Tinv t   -> Phase (fromDyadic $ dyadic 7 2) [t]

-- | Retrieve the path sum representation of a primitive gate
extractionAction :: ExtractionGates -> Pathsum DMod2
extractionAction gate = case gate of
  Hadamard _     -> hgate
  Phase theta xs -> rzNgate theta $ length xs
  MCT xs _       -> mctgate $ length xs

-- | Apply a circuit to a state
applyExtract :: Pathsum DMod2 -> [ExtractionGates] -> ExtractionState (Pathsum DMod2)
applyExtract sop xs = do
  ctx <- gets snd
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

extract :: ExtractionState a -> Map ID Int -> (a, [ExtractionGates])
extract st = runWriter . evalStateT st . mkctx

testCircuit :: [Primitive]
testCircuit = [H "y", CNOT "x" "y", T "y", CNOT "x" "y", H "x"]

bianCircuit :: [Primitive]
bianCircuit = (circ ++ circ) where
  circ = [CNOT "x" "y", X "x", T "y", H "y", T "y", H "y", Tinv "y",
          CNOT "x" "y", X "x", T "y", H "y", Tinv "y", H "y", Tinv "y"]

-- Need strength reduction
srCase :: [Primitive]
srCase = [CNOT "x" "y", H "x"] ++ cs "x" "y"

-- Need linear substitutions in the output for this case
hardCase :: [Primitive]
hardCase = [Tinv "y", CNOT "x" "y", H "x"] ++ cs "x" "y"

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

-- QFT
qft :: Int -> [Primitive]
qft 1 = [H "x1"]
qft n = [H ("x" ++ show n)] ++ concatMap (go n) (reverse [1..(n-1)]) ++ qft (n-1) where
  go n i  = crk (dMod2 1 (n - i)) ("x" ++ show i) ("x" ++ show n)
  crk theta x y =
    let angle = half * theta in
      [Rz (Discrete angle) x, Rz (Discrete angle) y, CNOT x y, Rz (Discrete $ -angle) y, CNOT x y]

qftFull :: Int -> [Primitive]
qftFull n = qft n ++ permute where
  permute = map (\(i, j) -> Swap i j) pairs
  pairs   = zip ["x" ++ show i | i <- [0..(n-1)`div`2]]
                ["x" ++ show i | i <- reverse [(n+1)`div`2..(n-1)]]

-- | Checks that the path sum of a Clifford+T circuit is indeed Unitary
prop_Unitary_is_Unitary :: CliffordT -> Bool
prop_Unitary_is_Unitary (CliffordT xs) = isUnitary $ simpleAction xs

-- | Checks that frame change is reversible
prop_Frame_Reversible :: CliffordT -> Bool
prop_Frame_Reversible (CliffordT xs) = sop == revertFrame subs localSOP where
  sop              = grind $ simpleAction xs
  (subs, localSOP) = changeFrame sop

-- | Checks that extraction always succeeds for a unitary path sum
prop_Clifford_plus_T_Extraction_Possible :: CliffordT -> Bool
prop_Clifford_plus_T_Extraction_Possible (CliffordT xs) = isJust (resynthesizeCircuit xs)

-- | Checks that the translation from Clifford+T to MCT is correct
prop_Translation_Correct :: CliffordT -> Bool
prop_Translation_Correct (CliffordT xs) = grind sop == grind sop' where
  (sop, ctx) = runState (computeAction xs) Map.empty
  sop'       = fst $ extract (applyExtract (identity $ Map.size ctx) (map toExtraction xs)) ctx

-- | Checks that affine simplifications are correct
prop_Affine_Correctness :: CliffordT -> Bool
prop_Affine_Correctness (CliffordT xs) = grind sop' == grind sop'' where
  (sop, ctx)    = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  (sop', gates) = extract (affineSimplifications sop) ctx
  (sop'', _)    = extract (applyExtract sop gates) ctx

-- | Checks that phase simplifications are correct
prop_Phase_Correctness :: CliffordT -> Bool
prop_Phase_Correctness (CliffordT xs) = grind sop' == grind sop'' where
  (sop, ctx)    = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  (sop', gates) = extract (phaseSimplifications sop) ctx
  (sop'', _)    = extract (applyExtract sop gates) ctx

-- | Checks that nonlinear simplifications are correct
prop_Nonlinear_Correctness :: CliffordT -> Bool
prop_Nonlinear_Correctness (CliffordT xs) = grind sop' == grind sop'' where
  (sop, ctx)    = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  (sop', gates) = extract (nonlinearSimplifications sop) ctx
  (sop'', _)    = extract (applyExtract sop gates) ctx

-- | Checks that strength reduction is correct
prop_Strength_Reduction_Correctness :: CliffordT -> Bool
prop_Strength_Reduction_Correctness (CliffordT xs) = grind sop' == grind sop'' where
  (sop, ctx)    = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  (sop', gates) = extract (strengthReduction sop) ctx
  (sop'', _)    = extract (applyExtract sop gates) ctx

-- | Checks that each step of the synthesis algorithm is correct
prop_Frontier_Correctness :: CliffordT -> Bool
prop_Frontier_Correctness (CliffordT xs) = grind sop' == grind sop'' where
  (sop, ctx)    = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  (sop', gates) = extract (synthesizeFrontier sop) ctx
  (sop'', _)    = extract (applyExtract sop gates) ctx

-- | Checks that the overall algorithm is correct
prop_Extraction_Correctness :: CliffordT -> Bool
prop_Extraction_Correctness (CliffordT xs) = go where
  (sop, ctx) = (\(sop, ctx) -> (grind sop, ctx)) $ runState (computeAction xs) Map.empty
  gates      = extractUnitary (mkctx ctx) sop
  go         = case gates of
    Nothing  -> True
    Just xs' ->
      let sop' = grind $ fst $ extract (applyExtract (identity $ outDeg sop) xs') ctx in
        sop == sop' || isTrivial (grind $ sop .> PS.dagger sop')

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

spec :: Spec
spec = return ()
