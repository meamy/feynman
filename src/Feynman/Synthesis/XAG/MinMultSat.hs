{-# LANGUAGE ImportQualifiedPost #-}

module Feynman.Synthesis.XAG.MinMultSat
  ( synthesizeFromFormulas,
    truthTableFormula,
  )
where

import Control.Monad
import Control.Monad.State.Strict (State, evalState, get, gets, modify, put, runState)
import Data.Bits
import Data.List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (mapMaybe)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import SAT.MiniSat

data FormulaAlloc = FormulaAlloc {nextVar :: Int}

data XAGBuilder = XAGBuilder {xagNodesRev :: [XAG.Node], nextNodeID :: Int}

type FormulaState a = State FormulaAlloc a

type XAGState a = State XAGBuilder a

freshVar :: FormulaState Int
freshVar = do
  v <- gets nextVar
  modify (\s -> s {nextVar = v + 1})
  return v

freshVars :: Int -> FormulaState [Int]
freshVars n = do
  vStart <- gets nextVar
  modify (\s -> s {nextVar = vStart + n})
  return [vStart .. vStart + n - 1]

freshNodeID :: XAGState Int
freshNodeID = do
  nID <- gets nextNodeID
  modify (\s -> s {nextNodeID = nID + 1})
  return nID

buildConstNode :: Bool -> XAGState Int
buildConstNode val = do
  nID <- gets nextNodeID
  modify (\s -> s {xagNodesRev = XAG.Const nID val : xagNodesRev s, nextNodeID = nID + 1})
  return nID

buildXorNode :: Int -> Int -> XAGState Int
buildXorNode xID yID = do
  nID <- gets nextNodeID
  modify (\s -> s {xagNodesRev = XAG.Xor nID xID yID : xagNodesRev s, nextNodeID = nID + 1})
  return nID

buildAndNode :: Int -> Int -> XAGState Int
buildAndNode xID yID = do
  nID <- gets nextNodeID
  modify (\s -> s {xagNodesRev = XAG.And nID xID yID : xagNodesRev s, nextNodeID = nID + 1})
  return nID

-- The output formulas should relate all possible assignments of input
-- variables to output values
synthesizeFromFormulas :: [Int] -> [Formula Int] -> Int -> XAG.Graph
synthesizeFromFormulas inputVars outputFormulas varsStart =
  solveMultComplexityAtLeast 0
  where
    solveMultComplexityAtLeast m =
      case solve fullFormula of
        -- Found a working solution!
        Just assignments ->
          let (s, outputIDs) =
                runState
                  (fullXAGFunc assignments originalInputIDs)
                  (XAGBuilder [] (length inputVars + 1))
           in XAG.Graph (reverse (xagNodesRev s)) originalInputIDs outputIDs
        -- Can't do, expand search?
        Nothing -> solveMultComplexityAtLeast (m + 1)
      where
        originalInputIDs = [1 .. length inputVars]
        (fullFormula, fullXAGFunc) =
          evalState
            (FormulaAlloc varsStart)
            ( do
                (equivFmls, expandedInputFmls, intermedXAGFunc) <- ofComplexityFormula m (map Var inputVars)
                (outputEquivFmls, outputXAGFunc) <- finalAffineFormulas expandedInputFmls outputFormulas
                let xagFunc assignments inputIDs = do
                      expandedInputIDs <- intermedXAGFunc assignments inputIDs
                      outputXAGFunc assignments expandedInputIDs
                return (All (equivFmls ++ outputEquivFmls), xagFunc)
            )

    inputs = map Var inputVars

    finalAffineFormulas :: [Formula Int] -> [Formula Int] -> FormulaState ([Formula Int], Map Int Bool -> [Int] -> XAGState [Int])
    finalAffineFormulas expandedInputFmls outputFmls = do
      affineFormulaXAGFuncs <- mapM (const (affineFunctionFormula [expandedInputFmls])) outputFmls
      let (affineFmls, affineXAGFuncs) = unzip affineFormulaXAGFuncs
      let xagFunc assignments inputIDs = do
            outputNodeIDs <- mapM (\f -> f assignments inputIDs) affineXAGFuncs
            return outputNodeIDs
      return (zipWith (:<->:) affineFmls outputFmls, xagFunc)

    -- Unlike the below (andFormula, affineFunctionFormula), this function also
    -- returns a list of formulas for the inputs including all the intermediate
    -- multiplicative (And) outputs, so they can be together combined by
    -- different affine functions producing each of multiple overall outputs
    ofComplexityFormula :: Int -> [Formula Int] -> FormulaState ([Formula Int], [Formula Int], Map Int Bool -> [Int] -> XAGState [Int])
    ofComplexityFormula 0 inputFmls = do
      return ([], inputFmls, (\assignments inputIDs -> return inputIDs))
    ofComplexityFormula k inputFmls = do
      let (kLess1EquivFmls, kLess1ExpandedInputFmls, kLess1XAGFunc) =
            ofComplexityFormula (k - 1) inputFmls
      (andFml, andXAGFunc) <- andFormula kLess1ExpandedInputFmls
      andVar <- freshVar
      let expandedInputFmls = Var andVar : inputFmls
      let xagFunc assignments inputIDs = do
            kLess1IDs <- kLess1XAGFunc inputIDs
            -- returned IDs and also the expanded IDs put into andXAGFunc here
            -- should match the order in the ofComplexityFormula return and the
            -- call to andFormula above, respectively
            andID <- andXAGFunc kLess1IDs
            return (andID : kLess1IDs)
      return ((andFml :<->: andVar) : kLess1EquivFmls, andVar : kLess1ExpandedInputFmls, xagFunc)

    andFormula :: [Formula Int] -> FormulaState (Formula Int, Map Int Bool -> [Int] -> XAGState Int)
    andFormula inputFmls = do
      (leftFormula, leftXAGFunc) <- affineFunctionFormula [inputFmls]
      (rightFormula, rightXAGFunc) <- affineFunctionFormula [inputFmls]
      let xagFunc assignments inputIDs = do
            leftNodeID <- leftXAGFunc assignments inputIDs
            rightNodeID <- rightXAGFunc assignments inputIDs
            andID <- buildAndNode leftNodeID rightNodeID
            return andID
      return (leftFormula :&&: rightFormula, xagFunc)

    affineFunctionFormula :: [Formula Int] -> FormulaState (Formula Int, Map Int Bool -> [Int] -> XAGState Int)
    affineFunctionFormula inputFmls = do
      ctlVars <- freshVars (length inputFmls)
      let terms = zipWith (\ctl input -> Var ctl :&&: input) ctlVars inputFmls
      let foldTerms [] = undefined
          foldTerms [term] = term
          foldTerms (term : remain) = term :++: foldTerms remain
      let xagFunc assignments inputIDs = do
            foldM buildXorNode (head usedInputIDs) (tail usedInputIDs)
            where
              usedInputIDs = ((map snd) . (filter (assignments Map.!))) (zip ctlVars inputIDs)
      return (foldTerms terms, xagFunc)

truthTableFormula :: (Ord v) => Formula v -> [Bool] -> Formula v
truthTableFormula outputVar truthTable inputVars =
  All (zipWith rowClause [0 ..] truthTable)
  where
    rowClause i True = All (bitsToFormulas i inputVars) :->: outputVar
    rowClause i False = All (bitsToFormulas i inputVars) :->: Not outputVar

    bitsToFormulas i vars =
      zipWith (\t v -> if i .&. t /= 0 then v else Not v) [1 `shiftL` k | k <- [0 ..]] vars
