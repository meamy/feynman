module Specs.TestUtil where

import Control.Monad (foldM, replicateM)
import Data.Bits
import Data.Foldable (foldl')
import Data.Functor ((<&>))
import Data.IntSet qualified as IntSet
import Data.Map (Map, (!))
import Data.Map qualified as Map
import Debug.Trace (trace)
import Feynman.Algebra.Base
import Feynman.Algebra.Pathsum.Balanced hiding (trace)
import Feynman.Algebra.Polynomial.Multilinear
import Feynman.Control
import Feynman.Core
import Feynman.Synthesis.Pathsum.Util
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.Util
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

evalMCTs :: [ExtractionGates] -> [(ID, Bool)] -> [(ID, Bool)]
evalMCTs gates initVals =
  Map.toList (foldl' evalMCT (Map.fromList initVals) gates)
  where
    evalMCT ctx (MCT controls target) =
      Map.insert target (ctx ! target /= all (ctx !) controls) ctx
    evalMCT ctx (Swapper xID yID) =
      Map.insert xID yVal (Map.insert yID xVal ctx)
      where
        xVal = ctx ! xID
        yVal = ctx ! yID

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

generateXAG :: Gen XAG.Graph
generateXAG = do
  sz <- max 1 <$> getSize
  let iosz = max (ceiling . sqrt . fromIntegral $ sz) 1
  nc <- chooseInt (1, max sz 1)
  oc <- chooseInt (1, iosz)
  ns <- mapM genNode [iosz .. iosz + sz]
  os <- replicateM oc (chooseInt (1, max nc 1))
  let coverNs = XAG.cover (IntSet.fromList os) ns
      insSet = XAG.freeVariables coverNs (IntSet.fromList os)
  return
    ( XAG.Graph
        { XAG.nodes = coverNs,
          XAG.inputIDs = IntSet.toList insSet,
          XAG.outputIDs = os
        }
    )
  where
    genNode i =
      oneof
        [ XAG.Const i <$> chooseAny,
          XAG.Not i <$> chooseInt (0, i - 1),
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.Xor i xID yID,
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.Xor i xID yID,
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.Xor i xID yID,
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.And i xID yID,
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.And i xID yID,
          do xID <- chooseInt (0, i - 1); yID <- chooseInt (0, i - 1); return $ XAG.And i xID yID
        ]

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
