{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Avoid lambda" #-}

module Feynman.Synthesis.XAG.MinMultSat
  ( resynthesizeMinMultSat,
    synthesizeFromTruthTable,
  )
where

import Control.Applicative (liftA2)
import Control.Exception (assert)
import Control.Monad (foldM, replicateM)
import Control.Monad.State.Strict (State, gets, modify, runState)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (intercalate)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Debug.Trace (trace)
import Feynman.Synthesis.XAG.Graph qualified as XAG
import Feynman.Synthesis.XAG.Simplify qualified as XAG
import Feynman.Synthesis.XAG.Subgraph qualified as XAG
import SAT.MiniSat

resynthesizeMinMultSat :: XAG.Graph -> Maybe XAG.Graph
resynthesizeMinMultSat g =
  trace ("Resynthesizing " ++ show g) $
    -- trace ("Truth table:\n  " ++ intercalate "\n  " (map show truthTable)) $
    trace ("  fullSubG = " ++ show fullSubG) $
      trace ("  trivAffine = " ++ show trivAffineSubGs) $
        (Just . XAG.subgraphToGraph)
          =<< foldr (liftA2 XAG.mergeSubgraphs) (Just affineSubG) minMultSubGs
  where
    -- If we wanted to minimize the affine portions (particularly any
    -- redundancy), it would make sense to combine everything here and simplify

    minMultSubGs = map resynthesize (partitionSeparable trivAffineRemainSubG) -- synthesizeFromTruthTable nInputs nOutputs truthTable
    affineSubG = foldr XAG.mergeSubgraphs XAG.emptySubgraph (trivAffineSubGs ++ nontrivAffineSubGs)
    (nontrivAffineSubGs, nontrivAffineRemainSubG) = separateNontrivialAffine trivAffineRemainSubG
    (trivAffineSubGs, trivAffineRemainSubG) = separateTrivialAffine fullSubG

    fullSubG = XAG.subgraphFromGraph g

    resynthesize :: XAG.Subgraph -> Maybe XAG.Subgraph
    resynthesize subG =
      resynthesizeAux 1
      where
        resynthesizeAux :: Int -> Maybe XAG.Subgraph
        resynthesizeAux multComplexity =
          case tryResynthesize multComplexity subG of
            Just minSubG -> Just minSubG
            Nothing ->
              if multComplexity < (IntMap.size (XAG.subInputIDs subG) + 1)
                then resynthesizeAux (multComplexity + 1)
                else Nothing

    partitionSeparable :: XAG.Subgraph -> [XAG.Subgraph]
    partitionSeparable subG = [subG]

    separateNontrivialAffine :: XAG.Subgraph -> ([XAG.Subgraph], XAG.Subgraph)
    separateNontrivialAffine subG =
      (affineSubgraphs, XAG.coverSubgraph subG nonAffineOutIdxs)
      where
        nonAffineOutIdxs =
          IntSet.toList
            ( IntSet.difference
                (IntMap.keysSet (XAG.subOutputIDs subG))
                (IntSet.fromList (concatMap (IntMap.keys . XAG.subOutputIDs) affineSubgraphs))
            )

        affineSubgraphs = mapMaybe tryResynthesizeAffineOutput (IntMap.keys (XAG.subOutputIDs subG))
        tryResynthesizeAffineOutput outIdx = tryResynthesize 0 (XAG.coverSubgraph subG [outIdx])

    tryResynthesize :: Int -> XAG.Subgraph -> Maybe XAG.Subgraph
    tryResynthesize multComplexity subG =
      reconstituteSubgraph
        <$> synthesizeFromTruthTable multComplexity (length inIdxs) (length outIdxs) tt
      where
        reconstituteSubgraph g =
          -- XAG.outputIDs = outIDs
          XAG.Subgraph
            { XAG.subNodes = XAG.nodes g,
              XAG.subInputIDs = IntMap.fromList (zip inIdxs (XAG.inputIDs g)),
              XAG.subOutputIDs = IntMap.fromList (zip outIdxs (XAG.outputIDs g))
            }
        (tt, inIdxs, outIdxs) = truthTableFromSubgraph subG

    separateTrivialAffine :: XAG.Subgraph -> ([XAG.Subgraph], XAG.Subgraph)
    separateTrivialAffine subG =
      (trivSlices, XAG.coverSubgraph subG (IntSet.toList nonTrivIdxs))
      where
        nonTrivIdxs = IntSet.difference (IntSet.fromAscList allOutIdxs) (IntSet.fromAscList trivIdxs)
        (trivIdxs, trivSlices) = unzip (filter (triviallyAffine . snd) sliceSubGs)
        sliceSubGs = map (\idx -> (idx, XAG.coverSubgraph subG [idx])) allOutIdxs

        triviallyAffine :: XAG.Subgraph -> Bool
        triviallyAffine subG = all notAndNode (XAG.subNodes subG)
          where
            notAndNode (XAG.And {}) = False
            notAndNode _ = True

        allOutIdxs = IntMap.keys (XAG.subOutputIDs subG)

truthTableFromSubgraph :: XAG.Subgraph -> ([([Bool], [Bool])], [Int], [Int])
truthTableFromSubgraph subG =
  ( [ (inputs, XAG.evalSubgraphPackedInOut subG inputs)
      | inputs <- ttInputs (IntMap.size (XAG.subInputIDs subG))
    ],
    IntMap.keys (XAG.subInputIDs subG),
    IntMap.keys (XAG.subOutputIDs subG)
  )

truthTableFromGraph :: XAG.Graph -> [([Bool], [Bool])]
truthTableFromGraph g =
  [(inputs, XAG.eval g inputs) | inputs <- ttInputs (length (XAG.inputIDs g))]

ttInputs :: Int -> [[Bool]]
ttInputs 0 = []
ttInputs 1 = [[False], [True]]
ttInputs n = [v : l | v <- [False, True], l <- ttInputs (n - 1)]

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
emptyFormulaBuilder nInputs =
  FormulaBuilder
    { nextVar = 1,
      nextInput = -(nInputs + 1),
      nFreeInputs = nInputs,
      computedInputsRev = []
    }

type FormulaState a = State FormulaBuilder a

freshParams :: Int -> FormulaState [Param]
freshParams n = do
  vStart <- gets nextVar
  modify (\s -> s {nextVar = vStart + n})
  return $ map Param [vStart .. vStart + n - 1]

addComputedInput :: FormulaFunc -> XAGFunc -> FormulaState Input
addComputedInput formulaFunc xagFunc = do
  i <- gets nextInput
  modify
    ( \s ->
        s
          { nextInput = i - 1,
            computedInputsRev = (Input i, formulaFunc, xagFunc) : computedInputsRev s
          }
    )
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

    withComputedInputFormula ctx input fml =
      ctx {inputFormulas = Map.insert input fml (inputFormulas ctx)}

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
synthesizeFromTruthTable :: Int -> Int -> Int -> [([Bool], [Bool])] -> Maybe XAG.Graph
synthesizeFromTruthTable multComplexity nInputs nOutputs truthTable =
  trace ("Searching MC " ++ show multComplexity) $
    case solve fullFormula of
      -- Found a working solution!
      Just assignments ->
        trace "Solved, building XAG" $
          let (outputIDs, s) = runState fullXAGFunc (emptyXAGBuilder assignments)
           in Just $ XAG.Graph (reverse (xagNodesRev s)) freeInputIDs outputIDs
      -- Can't do, expand search?
      Nothing -> Nothing
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

    fullFormulaClauses = concatMap (uncurry ttRowClauses) truthTable

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
      outputFuncs <- replicateM nOutputs affineFormula
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
        inIDs <- mapM (\i -> gets (inputNodeID i)) inputs
        used <- mapM (\p -> gets (paramAssignment p)) params
        case [i | (i, u) <- zip inIDs used, u] of
          [] -> buildConstNode False
          first : rest -> foldM buildXorNode first rest
  return (formulaFunc, xagFunc)
