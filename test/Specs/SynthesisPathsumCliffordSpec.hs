module Specs.SynthesisPathsumCliffordSpec where

import Test.Hspec

import Feynman.Core
import qualified Feynman.Core as Core
import Feynman.Algebra.Pathsum.Balanced
import Feynman.Synthesis.Pathsum.Clifford
import Feynman.Verification.Symbolic

import Arbitrary.Clifford

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


spec :: Spec
spec = return ()
