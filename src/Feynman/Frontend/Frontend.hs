{-# LANGUAGE DeriveGeneric #-}

module Feynman.Frontend.Frontend
  ( Pass (..),
    ProgramStats (..),
    ProgramRepresentation (..),
    statsLines,
  )
where

import Data.Map.Lazy (Map, toList)
import Feynman.Core (ID)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Maybe (maybeToList)

data Pass
  = Triv
  | Inline
  | Unroll
  | MCT
  | CT
  | Simplify
  | Phasefold
  | PauliFold Int
  | Statefold Int
  | CNOTMin
  | TPar
  | Cliff
  | CZ
  | CX
  | Decompile
  deriving (Eq, Read, Show, Generic)

data ProgramStats = ProgramStats
  { gateCounts :: Map ID Int,
    bitCount :: Maybe Int,
    qubitCount :: Int,
    gateDepth :: Maybe Int,
    tDepth :: Maybe Int
  }
  deriving (Eq, Read, Show, Generic)

instance NFData Pass
instance NFData ProgramStats

statsLines :: ProgramStats -> [String]
statsLines stats =
  let counts = map (\(gate, count) -> gate ++ ": " ++ show count) $ toList (gateCounts stats)
      bc = map (("Bits: " ++) . show) (maybeToList . bitCount $ stats)
      qbc = ["Qubits: " ++ (show . qubitCount $ stats)]
      gd = map (("Depth: " ++) . show) (maybeToList . gateDepth $ stats)
      td = map (("T depth: " ++) . show) (maybeToList . tDepth $ stats)
   in qbc ++ counts ++ gd ++ td

-- For now representation approximately equals syntax, but in future we maybe design a common IR
class ProgramRepresentation a where
  readAndParse :: String -> IO (Either String a)
  expectValid :: a -> Either String ()
  applyPass :: Bool -> Pass -> (a -> a)
  prettyPrint :: a -> String
  prettyPrintWithBenchmarkInfo :: String -> Float -> ProgramStats -> ProgramStats -> Bool -> a -> String
  computeStats :: a -> ProgramStats
  equivalenceCheck :: a -> a -> Either String a
