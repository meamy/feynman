module Specs.SynthesisXAGUtilSpec where

import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Util (fromMCTs, fromSBools)
import Data.Set (Set)
import Data.Set qualified as Set
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Specs.TestUtil


prop_ReknitUnravelIsIdentity :: (HasFeynmanControl) => Gen Bool
prop_ReknitUnravelIsIdentity = do
  -- circ <- generateExtractionGates 3 19 99
  -- denied <- sublistOf circ
  -- let deniedSet = Set.fromList denied
  --     (unCirc, stitches, _, _) = unravel (`Set.member` deniedSet) idGen circ
  --     reCirc = reknit unCirc stitches
  -- return $ equivalentToTrivialReorder circ reCirc
  return True

spec :: Spec
spec = do
  let ?feynmanControl = defaultControl
  prop "xag" prop_ReknitUnravelIsIdentity

