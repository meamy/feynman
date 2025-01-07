{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.MinMultSat
  ( synthesizeFromTruthTable,
  )
where

-- import Data.IntMap.Strict qualified as IntMap
-- import Data.IntSet qualified as IntSet
-- import Data.List (sort)
-- import Data.Maybe (isNothing, mapMaybe)
import Data.Bits
import Feynman.Synthesis.XAG.Graph qualified as XAG
import SAT.MiniSat

synthesizeFromTruthTable :: Int -> Int -> [[Bool]] -> XAG.Graph
synthesizeFromTruthTable numInputs numOutputs truthTables =
  solveComplexityAtLeast 0
  where
    solveComplexityAtLeast k =
      case solve (All (ttClause : [])) of
        Just assignment -> assignmentToXAG assignment
        Nothing -> solveComplexityAtLeast (k + 1)
      where
        assignmentToXAG assignment =
          XAG.Graph
            (XAG.Const 0 True : (map affineVars))
            [1 .. numInputs]
            []

        ttClause = All (map (uncurry singleOutputTTClause) (zip outputVars truthTables))
          where
            singleOutputTTClause outputVar truthTable =
              zipWith (curry rowClause) [0 ..] truthTable
              where
                rowClause i o = bitsToClause i inputVars :<->: bitsToClause (fromInteger o) [outputVar]
                bitsToClause i vars =
                  zipWith (\t v -> if i .&. t /= 0 then Var v else Not (Var v)) [1 `shiftL` k | k <- [0 ..]] vars

        multiplicativeVars :: Int -> [Int]
        multiplicativeVars i = undefined

    inputVars :: [Int]
    inputVars = [1 .. numInputs]
