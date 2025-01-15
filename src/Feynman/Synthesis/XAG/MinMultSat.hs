{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Avoid lambda" #-}

module Feynman.Synthesis.XAG.MinMultSat
  ( resynthesizeMinMultSat,
    synthesizeFromTruthTable,
  )
where

import Control.Exception (assert)
import Control.Monad (foldM, replicateM)
import Control.Monad.State.Strict (State, gets, modify, runState)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (intercalate)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe)
import Debug.Trace (trace)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import SAT.MiniSat

resynthesizeMinMultSat :: XAG.Graph -> Maybe XAG.Graph
resynthesizeMinMultSat g =
  -- trace ("Resynthesizing " ++ show g) $
  trace ("Truth table:\n  " ++ intercalate "\n  " (map show truthTable)) $
    synthesizeFromTruthTable nInputs nOutputs truthTable
  where
    nInputs = length (XAG.inputIDs g)
    nOutputs = length (XAG.outputIDs g)

    ttInputs 0 = []
    ttInputs 1 = [[False], [True]]
    ttInputs n = [v : l | v <- [False, True], l <- ttInputs (n - 1)]

    truthTable = [(inputs, fromJust (XAG.eval g inputs)) | inputs <- ttInputs nInputs]

newtype Param = Param Int deriving (Ord, Eq, Show)

newtype Input = Input Int deriving (Ord, Eq, Show)

type ParamFormula = Formula Param

type FormulaFunc = FormulaContext -> ParamFormula

type XAGFunc = XAGState Int

data FormulaBuilder = FormulaBuilder
  { nextVar :: Int,
    nextInput :: Int,
    nFreeInputs :: Int,
    computedInputsRev :: [(Input, FormulaFunc, XAGFunc)]
  }

emptyFormulaBuilder :: Int -> FormulaBuilder
emptyFormulaBuilder nInputs = FormulaBuilder {nextVar = 1, nextInput = -(nInputs + 1), nFreeInputs = nInputs, computedInputsRev = []}

type FormulaState a = State FormulaBuilder a

freshParams :: Int -> FormulaState [Param]
freshParams n = do
  vStart <- gets nextVar
  modify (\s -> s {nextVar = vStart + n})
  return $ map Param [vStart .. vStart + n - 1]

addComputedInput :: FormulaFunc -> XAGFunc -> FormulaState Input
addComputedInput formulaFunc xagFunc = do
  i <- gets nextInput
  modify (\s -> s {nextInput = i - 1, computedInputsRev = (Input i, formulaFunc, xagFunc) : computedInputsRev s})
  return $ Input i

freeInputs :: FormulaBuilder -> [Input]
freeInputs builder = map (Input . negate) [1 .. nFreeInputs builder]

allInputs :: FormulaBuilder -> [Input]
allInputs builder = freeInputs builder ++ [i | (i, _, _) <- reverse (computedInputsRev builder)]

newtype FormulaContext = FormulaContext {inputFormulas :: Map Input ParamFormula} deriving (Eq, Show)

inputFormula :: FormulaContext -> Input -> ParamFormula
inputFormula ctx input = inputFormulas ctx Map.! input

fixFormula :: Map Input ParamFormula -> [(Input, FormulaFunc, XAGFunc)] -> FormulaFunc -> ParamFormula
fixFormula fixingInputs compInputs fmlFunc = do
  fixFormulaRec compInputs (FormulaContext fixingInputs)
  where
    fixFormulaRec :: [(Input, FormulaFunc, XAGFunc)] -> FormulaContext -> ParamFormula
    fixFormulaRec [] ctx = fmlFunc ctx
    fixFormulaRec ((input, compFml, _) : remain) ctx =
      Let (compFml ctx) (\fml -> fixFormulaRec remain (withComputedInputFormula ctx input computed))
      where
        computed = compFml ctx

    withComputedInputFormula ctx input fml = ctx {inputFormulas = Map.insert input fml (inputFormulas ctx)}

data XAGBuilder = XAGBuilder
  { xagNodesRev :: [XAG.Node],
    nextNodeID :: Int,
    paramAssignmentsMap :: Map Param Bool,
    inputNodeIDsMap :: Map Input Int
  }

type XAGState a = State XAGBuilder a

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

paramAssignment :: Param -> XAGBuilder -> Bool
paramAssignment param ctx = fromMaybe False (Map.lookup param (paramAssignmentsMap ctx))

inputNodeID :: Input -> XAGBuilder -> Int
inputNodeID input ctx = inputNodeIDsMap ctx Map.! input

mapComputedInputNode :: Input -> Int -> XAGState ()
mapComputedInputNode input nodeID = do
  modify (\s -> s {inputNodeIDsMap = Map.insert input nodeID (inputNodeIDsMap s)})

-- The output formulas should relate all possible assignments of input
-- variables to output values
synthesizeFromTruthTable :: Int -> Int -> [([Bool], [Bool])] -> Maybe XAG.Graph
synthesizeFromTruthTable nInputs nOutputs truthTable =
  trace ("affine outputs: " ++ show (IntMap.keys affineOutputGraphs)) $
    trace ("non-affine outputs: " ++ show nonAffineOutputs) $
      trace ("affine graphs:\n" ++ intercalate "\n" (map (("  " ++) . show) (IntMap.elems affineOutputGraphs))) $
        if null nonAffineOutputs
          then Just (mergeAffineGraphs (XAG.Graph [] [] []) (IntMap.toAscList affineOutputGraphs))
          else case solveNonAffine 1 of
            Just g -> Just (mergeAffineGraphs g (IntMap.toAscList affineOutputGraphs))
            Nothing -> Nothing
  where
    mergeAffineGraphs :: XAG.Graph -> [(Int, XAG.Graph)] -> XAG.Graph
    mergeAffineGraphs g [] = g
    mergeAffineGraphs g ((i, gAffine) : remain) =
      mergeAffineGraphs merged remain
      where
        merged = XAG.mergeAt freeInputIDs g freeInputIDs i gAffine freeInputIDs

    solveNonAffine :: Int -> Maybe XAG.Graph
    solveNonAffine multComplexity =
      trace ("Searching MC " ++ show multComplexity) $
        trace ("non-affine truth table [0]: " ++ show (nonAffineTruthTable !! 0)) $
          case solve fullFormula of
            -- Found a working solution!
            Just assignments ->
              trace "Solved, building XAG" $
                let (outputIDs, s) = runState fullXAGFunc (emptyXAGBuilder assignments)
                 in Just $ XAG.Graph (reverse (xagNodesRev s)) freeInputIDs outputIDs
            -- Can't do, expand search?
            Nothing ->
              if multComplexity >= 12
                then trace "Giving up." Nothing
                else solveNonAffine (multComplexity + 1)
      where
        fullXAGFunc :: XAGState [Int]
        fullXAGFunc = do
          _ <- snd (head funcPairs)
          mapM snd outputFuncPairs

        -- Const 0 would be False by convention, but that's never going to be needed
        emptyXAGBuilder assignments = XAGBuilder [XAG.Const 1 True] (nInputs + 2) assignments freeInputMap

        freeInputMap = Map.fromList (zip [Input (negate i) | i <- [1 .. nInputs]] freeInputIDs)

        fullFormula :: ParamFormula
        fullFormula =
          trace ("Full formula has " ++ show (length fullFormulaClauses) ++ " clauses") $
            All fullFormulaClauses

        fullFormulaClauses = concatMap (uncurry ttRowClauses) nonAffineTruthTable

        ttRowClauses :: [Bool] -> [Bool] -> [ParamFormula]
        ttRowClauses inputBools outputBools =
          -- trace ("fixed formulas:\n" ++ intercalate "\n" (map show fixedFormulas)) $
          zipWith matchExpectedOutputFml fixedFormulas outputBools
          where
            matchExpectedOutputFml resultFml True = resultFml
            matchExpectedOutputFml resultFml False = Not resultFml

            fixedFormulas = map (fixFormula fixingInputs (reverse (computedInputsRev builder)) . fst) outputFuncPairs
            fixingInputs = Map.fromList [(input, if b then Yes else No) | (input, b) <- zip (freeInputs builder) inputBools]

        -- The first function is the common k-complexity one, which is not
        -- really an output to the caller
        outputFuncPairs = drop 1 funcPairs
        (funcPairs, builder) = runState outputFormulas (emptyFormulaBuilder nInputs)

        outputFormulas :: FormulaState [(FormulaFunc, XAGFunc)]
        outputFormulas = do
          kcFuncs <- addKComplexityInputs multComplexity
          outputFuncs <- replicateM (length nonAffineOutputs) affineFormula
          return $ kcFuncs : outputFuncs

        addKComplexityInputs :: Int -> FormulaState (FormulaFunc, XAGFunc)
        addKComplexityInputs 0 = return (return No, buildConstNode False)
        addKComplexityInputs k = do
          _ <- addKComplexityInputs (k - 1)
          (andFmlFunc, andXAGFunc) <- andFormula
          input <- addComputedInput andFmlFunc andXAGFunc
          let xagFunc = do
                nodeID <- andXAGFunc
                mapComputedInputNode input nodeID
                return nodeID
          return (andFmlFunc, xagFunc)

    freeInputIDs = [2 .. nInputs + 1]

    nonAffineTruthTable :: [([Bool], [Bool])]
    nonAffineTruthTable =
      if null affineOutputGraphs
        then truthTable
        else map (\(ins, outs) -> (ins, map (outs !!) nonAffineOutputs)) truthTable
    nonAffineOutputs = [i | i <- [0 .. nOutputs - 1], IntMap.notMember i affineOutputGraphs]
    affineOutputGraphs :: IntMap XAG.Graph
    affineOutputGraphs = synthesizeAffineFromTruthTable nInputs nOutputs truthTable

    -- Synthesize any outputs that are pure affine functions, to declutter the
    -- problem
    synthesizeAffineFromTruthTable :: Int -> Int -> [([Bool], [Bool])] -> IntMap XAG.Graph
    synthesizeAffineFromTruthTable nInputs nOutputs truthTable =
      foldl
        (\m i -> maybeInsertAffineSolution m i [(ins, outs !! i) | (ins, outs) <- truthTable])
        IntMap.empty
        [0 .. nOutputs - 1]
      where
        maybeInsertAffineSolution :: IntMap XAG.Graph -> Int -> [([Bool], Bool)] -> IntMap XAG.Graph
        maybeInsertAffineSolution m i singleTT =
          case solveAffine singleTT of
            Just g -> IntMap.insert i g m
            Nothing -> m

        solveAffine :: [([Bool], Bool)] -> Maybe XAG.Graph
        solveAffine singleTT =
          case solve fullFormula of
            Just assignments ->
              trace "Solved, building XAG" $
                let (outputID, s) = runState xagFunc (emptyXAGBuilder assignments)
                 in Just $ XAG.Graph (reverse (xagNodesRev s)) freeInputIDs [outputID]
            Nothing -> Nothing
          where
            -- Const 0 would be False by convention, but that's never going to be needed
            emptyXAGBuilder assignments = XAGBuilder [XAG.Const 1 True] (nInputs + 2) assignments freeInputMap

            freeInputMap = Map.fromList (zip [Input (negate i) | i <- [1 .. nInputs]] freeInputIDs)
            freeInputIDs = [2 .. nInputs + 1]

            fullFormula = All (map (uncurry ttRowClause) singleTT)

            ttRowClause :: [Bool] -> Bool -> ParamFormula
            ttRowClause inputBools outputBool =
              if outputBool then fixedFormula else Not fixedFormula
              where
                fixedFormula = fixFormula fixingInputs (reverse (computedInputsRev builder)) formulaFunc
                fixingInputs = Map.fromList [(input, if b then Yes else No) | (input, b) <- zip (freeInputs builder) inputBools]

            ((formulaFunc, xagFunc), builder) = runState affineFormula (emptyFormulaBuilder nInputs)

-- The following formula generators produce two functions, one to construct a
-- formula that represents the parameterized output of this function, and the
-- other to construct the associated XAG node snippet.

-- When encoding a function for the SAT solve, we do not assign any variables
-- to the function input or output -- what we're solving for is the parameters
-- characterizing the function. For example, for an affine boolean function of
-- some set of potential inputs, the minimal parameters are a flag for each
-- potential input to say whether it's summed in, and then an extra flag for
-- whether the output is inverted (which you can omit if one of the potential
-- inputs is constant True).

-- Since the caller doesn't really want to have to know in advance the number
-- of parameters needed by any particular formula, we use a monadic idiom to
-- handle the allocation of fresh parameter variables. That's the FormulaState.
-- Then, the returned functions implicitly carry the mapping from allocated
-- variables to the necessary parts of the structures they generate. In the
-- case of the formula function, this is logical structures generated to say
-- (to the SAT solver) how any specific set of inputs is transformed given all
-- possible parameterizations; in the case of the XAG function, the specific
-- parameters are looked up in the assignments, and that drives the generation
-- of XAG nodes to compute the function for any possible inputs. The return of
-- the formula function is the entire formula, in the case of the XAG function
-- the nodes are written into the monadic state and the return is the node IDs
-- of the output nodes. In either case it's up to the caller to keep track of
-- who else subsequently may need this information.

-- It should be clear that if you want two (potentially) _different_ affine
-- functions, you need to generate two different formula functions so that they
-- will end up with distinct parameter variables, otherwise the SAT solve will
-- be forced to give them the same parameters.

-- The expectation is that the returned formula function will be called many
-- many times, but with different literal inputs. Unfortunately there's not a
-- way to reduce this repetitiveness -- it's integral to the process. Most (but
-- not all) of the input formulas will be different combinations of "Yes" and
-- "No" literals, with each row of the truth table potentially getting a
-- distinct combination of inputs. However, some of the inputs will be the
-- outputs of prior functions, and in those cases the caller may use "Let"
-- constructs to help keep the repetitiveness down. The point is, you can
-- optimize a little by specializing the clauses output if you spot a "Yes" or
-- "No", but just don't depend on that being the only thing you encounter.

andFormula :: FormulaState (FormulaFunc, XAGFunc)
andFormula = do
  (leftFmlFunc, leftXAGFunc) <- affineFormula
  (rightFmlFunc, rightXAGFunc) <- affineFormula
  let formulaFunc ctx = leftFmlFunc ctx :&&: rightFmlFunc ctx
  let xagFunc = do
        leftOutputID <- leftXAGFunc
        rightOutputID <- rightXAGFunc
        buildAndNode leftOutputID rightOutputID
  return (formulaFunc, xagFunc)

affineFormula :: FormulaState (FormulaFunc, XAGFunc)
affineFormula = do
  inputs <- gets allInputs
  params <- freshParams (length inputs)
  trace ("Allocated params " ++ show params) $ return ()
  let formulaFunc ctx =
        formulaFuncAux (filter (\(_, i) -> i /= No) (zip params (map (inputFormula ctx) inputs)))
        where
          formulaFuncAux [] = No
          formulaFuncAux [(v, Yes)] = Var v
          formulaFuncAux [(v, fml)] = Var v :&&: fml
          formulaFuncAux ((v, Yes) : remain) = Var v :++: formulaFuncAux remain
          formulaFuncAux ((v, fml) : remain) = (Var v :&&: fml) :++: formulaFuncAux remain
  let xagFunc = do
        inputIDs <- mapM (\i -> gets (inputNodeID i)) inputs
        used <- mapM (\p -> gets (paramAssignment p)) params
        case [i | (i, u) <- zip inputIDs used, u] of
          [] -> buildConstNode False
          first : rest -> foldM buildXorNode first rest
  return (formulaFunc, xagFunc)
