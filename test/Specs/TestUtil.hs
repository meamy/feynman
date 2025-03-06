module Specs.TestUtil where

import Data.Bits
import Data.Map (Map, (!))
import Data.Map qualified as Map
import Feynman.Algebra.Base
import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Util
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Algebra.Pathsum.Balanced hiding (trace)
import Data.Foldable (foldl')
import Debug.Trace (trace)

evalMCTs :: [ExtractionGates] -> [(ID, Bool)] -> [(ID, Bool)]
evalMCTs gates initVals =
  Map.toList (foldl' evalMCT (Map.fromList initVals) gates)
  where
    evalMCT ctx (MCT controls target) =
       Map.insert target (ctx ! target /= all (ctx !) controls) ctx

evalSBool :: SBool Var -> [(Var, Bool)] -> Bool
evalSBool sbool inputVals =
  foldl' (/=) False (map (all (Map.fromList inputVals !) . vars . snd) (toTermList sbool))

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

idGen :: [ID]
idGen = ['@' : show i | i <- [1 ..]]

genQubitParams :: Int -> Gen [ID]
genQubitParams n = do
  sz <- getSize
  let count = max 0 (min (sz - 1) n)
  rBits <- choose (0, (1 `shiftL` count) - 1) :: Gen Integer
  genQubitParamsAux (rBits .|. 1) allIdxs []
  where
    -- using rBits as a random source, select
    genQubitParamsAux rBits elems qubits
      | even rBits = return qubits
      | otherwise = do
          i <- choose (0, length elems - 1)
          let (ls, e : rs) = splitAt i elems
          genQubitParamsAux (rBits `shiftR` 1) (ls ++ rs) (q e : qubits)
    allIdxs = [0 .. n]

q :: Int -> ID
q idx = 'q' : show idx

generateMCTs :: Int -> Int -> Gen [ExtractionGates]
generateMCTs n k =
  resize k $ listOf1 genMCT
  where
    genMCT = do
      yxs <- genQubitParams n
      let y : xs = yxs
      return $ MCT xs y

-- | Generates a random circuit
generateExtractionGates :: Int -> Int -> Int -> Gen [ExtractionGates]
generateExtractionGates m n k =
  resize k $ listOf1 $ oneof [genHadamard, genMCT, genPhase, genSwapper]
  where
    genHadamard = do
      x <- chooseInt (0, n)
      return $ Hadamard (q x)
    genMCT = do
      yxs <- genQubitParams n
      let y : xs = yxs
      return $ MCT xs y
    genPhase = do
      xs <- genQubitParams n
      theta <- genDMod2
      return $ Phase 0 xs
    genSwapper = do
      x <- chooseInt (0, n)
      y <- chooseInt (0, n) `suchThat` (/= x)
      return $ Swapper (q x) (q y)
    genDMod2 = do
      x <- chooseInt (0, (1 `shiftL` m) - 2)
      return $ dMod2 (fromIntegral (x + 1)) m
