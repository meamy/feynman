module Feynman.Frontend.Frontend
  ( Pass (..),
    ProgramStats (..),
    ProgramRepresentation (..),
    statsLines,
  )
where

import Data.Map.Lazy (Map, toList)
import Feynman.Core (ID)

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

data ProgramStats = ProgramStats {gateCounts :: Map ID Int, qubitCount :: Int, gateDepth :: Int, tDepth :: Int}

statsLines :: ProgramStats -> [String]
statsLines stats =
  let counts = map (\(gate, count) -> gate ++ ": " ++ show count) $ toList (gateCounts stats)
      qbc = ["Qubits: " ++ (show . qubitCount $ stats)]
      gd = ["Depth: " ++ (show . gateDepth $ stats)]
      td = ["T depth: " ++ (show . tDepth $ stats)]
   in qbc ++ counts ++ gd ++ td

-- For now representation approximately equals syntax, but in future we maybe design a common IR
class ProgramRepresentation a where
  readAndParse :: String -> IO (Either String a)
  expectValid :: a -> Either String ()
  applyPass :: Pass -> (a -> a)
  prettyPrint :: a -> String
  prettyPrintWithBenchmarkInfo :: String -> Float -> ProgramStats -> ProgramStats -> a -> String
  computeStats :: a -> ProgramStats
  equivalenceCheck :: a -> a -> Either String a
