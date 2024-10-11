module Feynman.Frontend.OpenQASM3.Semantics where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Control.Monad.State as State
import Data.Int (Int64)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence.Internal.Sorting (QList (Nil))
import qualified Data.Set as Set
import Data.Word (Word64)
import Debug.Trace
import Feynman.Core
import Feynman.Frontend.OpenQASM3.Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import Feynman.Frontend.OpenQASM3.Syntax

type Ref = Int

nilRef = -1

firstRef = 1

isNilRef r = r < 0

data Context c = Context {ref :: Ref, sourceCtx :: c} deriving (Eq, Read, Show)

nilContext = Context nilRef Map.empty

data Property
  = ExprIsConst
  | ExprType TypeSpec
  deriving (Eq, Read, Show)

data TypeSpec
  = NilType
  | BitType Int -- size
  | IntType Int -- size
  | UintType Int -- size
  | FloatType Int -- size
  | AngleType Int -- size
  | BoolType
  | DurationType
  | StretchType
  | ComplexType TypeSpec -- base
  | QubitType Int -- size
  | HwQubitType Int -- hwindex
  | ArrayType TypeSpec [Int64] -- base, sizes
  | ArrayRefType Bool TypeSpec Int -- mutable, base, dim
  deriving (Eq, Read, Show)

data ConstantValue
  = -- NilValue used as bottom sometimes
    NilValue
  | BitValue Int Int64
  | IntValue Int Int64
  | UintValue Int Word64
  | FloatValue Int Double
  | AngleValue Int Double
  | BoolValue Bool
  | DurationValue Bool Double
  | ComplexValue Int Double Double
  | ArrayValue TypeSpec [Int64] [ConstantValue]
  deriving (Eq, Read, Show)

typeOfValue :: ConstantValue -> TypeSpec
typeOfValue (BitValue bits _) = BitType bits
typeOfValue (IntValue bits _) = IntType bits
typeOfValue (UintValue bits _) = UintType bits
typeOfValue (FloatValue bits _) = FloatType bits
typeOfValue (AngleValue bits _) = AngleType bits
typeOfValue (BoolValue _) = BoolType
typeOfValue (DurationValue stretch _) = DurationType
typeOfValue (ComplexValue bits _ _) = ComplexType (FloatType bits)
typeOfValue (ArrayValue elemType numsElems _) = ArrayType elemType numsElems

{- This table taken from OpenQASM3 documentation -- language/types.html
arccos   | float on [-1, 1] -> float on [0, pi]                                         | Inverse cosine.
arcsin   | float on [-1, 1] -> float on [-pi / 2, pi / 2]                               | Inverse sine.
arctan   | float -> float on [-pi / 2, pi / 2]                                          | Inverse tangent.
ceiling  | float -> float                                                               | Round to the nearest representable integer equal or greater in value.
cos      | (float or angle) -> float                                                    | Cosine.
exp      | float -> float; complex -> complex                                           | Exponential e ^x.
floor    | float -> float                                                               | Round to the nearest representable integer equal or lesser in value.
log      | float -> float                                                               | Logarithm base e.
mod      | int, int -> int; float, float -> float                                       | Modulus. The remainder from the integer division of the first argument by the second argument.
popcount | bit[_] -> uint                                                               | Number of set (1) bits.
pow      | int, uint -> int; float, float -> float; complex, complex -> complex         | pow(a, b) = a ^b. For floating-point and complex values, the principal value is returned.
rotl     | bit[n] value, int distance -> bit[n]; uint[n] value, int distance -> uint[n] | Rotate the bits in the representation of value by distance places to the left (towards higher indices). This is similar to a bit shift operation, except the vacated bits are filled from the overflow, rather than being set to zero. The width of the output is set equal to the width of the input. rotl(a, n) == rotr(a, -n).
rotr     | bit[n] value, int distance -> bit[n]; uint[n] value, int distance -> uint[n] | Rotate the bits in the representation of value by distance places to the right (towards lower indices).
sin      | (float or angle) -> float                                                    | Sine.
sqrt     | float -> float; complex -> complex                                           | Square root. This always returns the principal root.
tan      | (float or angle) -> float                                                    | Tangent.
-}

data Analysis c = Analysis {nextRef :: Int, nextSymbols :: Map.Map String Ref {-, sources :: Map.Map Ref c-}}
  deriving (Eq, Read, Show)

type SyntaxNode c = Node Tag c

type Result v = (Chatty.Chatty String String) v

type AnalysisResult c v = StateT (Analysis c) (Chatty.Chatty String String) v

analyzeFail :: String -> AnalysisResult c v
analyzeFail = lift . Chatty.fail

analyzePrepend :: String -> AnalysisResult c v -> AnalysisResult c v
analyzePrepend msg resm = do
  res <- resm
  lift $ Chatty.prepend msg (return res)

analyzeAppend :: AnalysisResult c v -> String -> AnalysisResult c v
analyzeAppend resm msg = do
  res <- resm
  lift $ Chatty.append (return res) msg

freshAnalysis :: Analysis c
freshAnalysis = Analysis 1 Map.empty

newContext :: c -> AnalysisResult c (Context c)
newContext c = do
  Analysis {nextRef = n, nextSymbols = syms} <- get
  modify (\s -> s {nextRef = n + 1})
  return $ Context n c

normalize :: SyntaxNode c -> Result (SyntaxNode c)
normalize (Node (Program _ _ tok) stmts ctx) =
  evalStateT
    ( do
        statements <- mapM normalizeStatement stmts
        return (Node (Program 3 (Just 1) EofToken) (concat statements) ctx)
    )
    freshAnalysis

normalizeStatement :: SyntaxNode c -> AnalysisResult c [SyntaxNode c]
normalizeStatement (Node Statement [] _) = return []
normalizeStatement (Node Statement (content : annotations) ctx) = do
  normContent <- normalizeStmtContent content
  unless (null annotations) (analyzeFail "Statement annotations are not supported")
  return $ map (\nc -> Node Statement [nc] ctx) normContent

-- expectAnnotation (Node (Annotation {}) _ _) = return ()
-- expectAnnotation (Node {tag = tag}) = analyzeFail ("expected Annotation, found " ++ show tag)

normalizeStmtContent :: SyntaxNode c -> AnalysisResult c [SyntaxNode c]
normalizeStmtContent (Node (Pragma ctnt _) [] _) =
  analyzePrepend "Ignoring \"pragma\" statement" $ return []
normalizeStmtContent (Node AliasDeclStmt (ident : exprs) _) = analyzeFail "\"alias\" statements are not supported"
normalizeStmtContent node@(Node (AssignmentStmt op) [target, expr] _) = do
  -- require assignable
  target <- normalizeLvalueExpr target
  -- require compatible types
  expr <- normalizeRvalueExpr expr
  return [node {children = [target, expr]}]
normalizeStmtContent (Node BarrierStmt gateOperands _) = analyzePrepend "Ignoring \"barrier\" statement" $ return []
normalizeStmtContent (Node BoxStmt [time, scope] _) =
  analyzePrepend "Treating \"box\" statement as scope" (normalizeStmtContent scope)
normalizeStmtContent node@(Node BreakStmt [] _) = trivialStatement node
normalizeStmtContent (Node (CalStmt calBlock) [] _) = analyzePrepend "Ignoring \"cal\" statement" $ return []
normalizeStmtContent (Node (DefcalgrammarStmt _ cgname) [] _) =
  analyzePrepend "Ignoring \"defcalgrammar\" statement" $ return []
normalizeStmtContent node@(Node ClassicalDeclStmt [declType, ident, maybeInitExpr] _) = do
  -- require classical type
  declType <- normalizeClassicalDeclType declType
  ident <- normalizeIdentifier ident
  maybeInitExpr <- normalizeRvalueExpr maybeInitExpr
  return [node {children = [declType, ident, maybeInitExpr]}]
normalizeStmtContent node@(Node ConstDeclStmt [declType, ident, initExpr] _) = do
  -- require scalar classical type
  declType <- normalizeClassicalDeclType declType
  ident <- normalizeIdentifier ident
  -- require not nil
  initExpr <- normalizeRvalueExpr initExpr
  return [node {children = [declType, ident, initExpr]}]
normalizeStmtContent node@(Node ContinueStmt [] _) = trivialStatement node
normalizeStmtContent node@(Node DefStmt [ident, argDefs, returnType, stmts] _) = do
  ident <- normalizeIdentifier ident
  returnType <- maybeNormalize normalizeClassicalDeclType NilNode returnType
  argDefs <- normalizeList normalizeArgumentDef argDefs
  -- require stmts is a scope
  return [node {children = [ident, argDefs, returnType, stmts]}]
  where
    normalizeArgumentDef node@(Node ArgumentDefinition [typeDecl, ident] _) = do
      typeDecl <- normalizeDeclType typeDecl
      ident <- normalizeIdentifier ident
      return node {children = [typeDecl, ident]}
normalizeStmtContent (Node DelayStmt (designator : gateOperands) _) =
  analyzePrepend "Ignoring \"delay\" statement" $ return []
normalizeStmtContent (Node DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  analyzePrepend "Ignoring \"defcal\" statement" $ return []
normalizeStmtContent (Node EndStmt [] _) = (lift . return) []
normalizeStmtContent node@(Node ExpressionStmt [expr] _) = do
  expr <- normalizeRvalueExpr expr
  return [node {children = [expr]}]
normalizeStmtContent (Node ExternStmt [ident, paramTypes, returnType] _) =
  analyzePrepend "Ignoring \"extern\" def statement" $ return []
normalizeStmtContent node@(Node ForStmt [declType, ident, range, loopStmt] _) = do
  declType <- normalizeClassicalDeclType declType
  ident <- normalizeIdentifier ident
  -- require either set, range, bit, or array expression
  -- require compatible type with declType
  range <- normalizeLoopRange range
  loopStmt <- normalizeStmtToScope loopStmt
  -- ensure loopStmt normalizes to a single statement!
  return [node {children = [declType, ident, range] ++ loopStmt}]
normalizeStmtContent node@(Node GateStmt [ident, params, qArgs, stmts] _) = do
  ident <- normalizeIdentifier ident
  params <- maybeNormalize (normalizeList normalizeIdentifier) NilNode params
  qArgs <- normalizeList normalizeIdentifier qArgs
  -- require stmts is a scope
  return [node {children = [ident, params, qArgs, stmts]}]
normalizeStmtContent node@(Node GateCallStmt [modifiers, target, maybeParams, maybeDuration, maybeQArgs] _) = do
  unless (isNilNode modifiers) (analyzeFail "Gate modifiers not supported")
  target <- normalizeIdentifier target
  maybeParams <- maybeNormalize (normalizeList normalizeRvalueExpr) NilNode maybeParams
  -- require duration is timespan
  maybeQArgs <- maybeNormalize (normalizeList normalizeQubitExpr) NilNode maybeQArgs
  return [node {children = [modifiers, target, maybeParams, maybeDuration, maybeQArgs]}]
normalizeStmtContent node@(Node IfStmt [condExpr, thenStmt, maybeElseStmt] _) = do
  -- require bool or compatible type
  condExpr <- normalizeRvalueExpr condExpr
  -- ensure thenStmt normalizes to a single statement!
  thenStmt <- normalizeStmtToScope thenStmt
  -- ensure maybeElseStmt normalizes to a single statement!
  maybeElseStmt <- maybeNormalize normalizeStmtToScope [NilNode] maybeElseStmt
  return [node {children = condExpr : thenStmt ++ maybeElseStmt}]
normalizeStmtContent (Node (IncludeStmt path _) [] _) = do
  unless (path == "stdgates.inc" || path == "qelib1.inc") (analyzeFail "TODO \"include\"")
  return []
normalizeStmtContent node@(Node InputIoDeclStmt [declType, ident] _) = do
  -- require classical type
  declType <- normalizeClassicalDeclType declType
  ident <- normalizeIdentifier ident
  return [node {children = [declType, ident]}]
normalizeStmtContent node@(Node OutputIoDeclStmt [declType, ident] _) = do
  -- require classical type
  declType <- normalizeClassicalDeclType declType
  ident <- normalizeIdentifier ident
  return [node {children = [declType, ident]}]
normalizeStmtContent node@(Node MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) = do
  -- require assignable
  maybeTgt <- normalizeLvalueExpr maybeTgt
  -- require compatible types
  msrExpr <- normalizeMeasureExpr msrExpr
  return [node {children = [msrExpr, maybeTgt]}]
normalizeStmtContent (Node CregOldStyleDeclStmt [ident, maybeSize] ctx) = do
  ident <- normalizeIdentifier ident
  -- require bitSize nil or literal number
  bitSize <-
    if isNilNode maybeSize
      then return (withContext ctx $ integerLiteralNode 1)
      else normalizeLiteralNumber maybeSize
  return [Node ClassicalDeclStmt [Node BitTypeSpec [bitSize] ctx, ident, NilNode] ctx]
normalizeStmtContent (Node QregOldStyleDeclStmt [ident, maybeSize] ctx) = do
  ident <- normalizeIdentifier ident
  -- require bitSize nil or literal number
  bitSize <-
    if isNilNode maybeSize
      then return (withContext ctx $ integerLiteralNode 1)
      else normalizeLiteralNumber maybeSize
  return [Node ClassicalDeclStmt [Node QubitTypeSpec [bitSize] ctx, ident, NilNode] ctx]
normalizeStmtContent node@(Node QuantumDeclStmt [qubitType, ident] _) = do
  -- qubitType <- normalizeQubitType qubitType
  ident <- normalizeIdentifier ident
  return [node {children = [qubitType, ident]}]
normalizeStmtContent node@(Node ResetStmt [qArgs] _) = do
  qArgs <- normalizeQubitExpr qArgs
  return [node {children = [qArgs]}]
normalizeStmtContent node@(Node ReturnStmt [maybeExpr] _) = do
  maybeExpr <- normalizeExpr maybeExpr
  return [node {children = [maybeExpr]}]
normalizeStmtContent node@(Node WhileStmt [condExpr, loopStmt] _) = do
  -- require bool or compatible type
  condExpr <- normalizeRvalueExpr condExpr
  -- ensure loopStmt normalizes to a single statement!
  loopStmt <- normalizeStmtToScope loopStmt
  return [node {children = condExpr : loopStmt}]
normalizeStmtContent node@(Node Scope stmts _) = do
  stmts <- mapM normalizeStatement stmts
  return [node {children = concat stmts}]
normalizeStmtContent node@(Node tag _ _) = error ("Ill-formed " ++ show tag ++ " node: " ++ pretty node)

normalizeStmtToScope :: Node Tag c -> AnalysisResult c [SyntaxNode c]
normalizeStmtToScope node@(Node Scope _ _) = normalizeStmtContent node
normalizeStmtToScope node@(Node Statement _ ctx) = return [Node Scope [node] ctx]

normalizeIdentifier :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeIdentifier = lift . return

removeParens :: SyntaxNode c -> SyntaxNode c
removeParens (Node ParenExpr [expr] _) = expr
removeParens (Node ParenExpr _ _) = error "ill-formed ParenExpr"
removeParens expr = expr

normalizeExpr :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeExpr expr = (lift . return) (removeParens expr)

normalizeLvalueExpr :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeLvalueExpr = normalizeExpr

normalizeRvalueExpr :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeRvalueExpr = normalizeExpr

normalizeQubitExpr :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeQubitExpr = normalizeExpr

normalizeMeasureExpr :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeMeasureExpr = normalizeExpr

normalizeLoopRange :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeLoopRange = normalizeExpr

normalizeLiteralNumber :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeLiteralNumber = normalizeExpr

normalizeDeclType :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeDeclType node@(Node QubitTypeSpec _ _) = return node
normalizeDeclType node = normalizeClassicalDeclType node

normalizeClassicalDeclType :: SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeClassicalDeclType expr = (lift . return) (removeParens expr)

normalizeList :: (SyntaxNode c -> AnalysisResult c (SyntaxNode c)) -> SyntaxNode c -> AnalysisResult c (SyntaxNode c)
normalizeList f NilNode = error "normalizeList on NilNode"
normalizeList f list@(Node List children _) = do
  children <- mapM f children
  return list {children = children}

maybeNormalize :: (SyntaxNode c -> AnalysisResult c v) -> v -> SyntaxNode c -> AnalysisResult c v
maybeNormalize f alt NilNode = return alt
maybeNormalize f alt node = f node

isAssignable :: TypeSpec -> TypeSpec -> Bool
isAssignable lvalueType rvalueType = True

typeOfExpression :: SyntaxNode c -> TypeSpec
typeOfExpression expr = NilType

trivialStatement :: SyntaxNode c -> AnalysisResult c [SyntaxNode c]
trivialStatement stmt = lift $ return [stmt]

{-
-- normalizeStmtContent node@(Node (AssignmentStmt op) [target, expr] _) = do
--   unless (op == DoubleEqualsToken) (analyzeFail "ill-formed assignment statement")
--   target <- normalizeLvalueExpr target
--   expr <- normalizeRvalueExpr expr
--   unless (assignable (typeOfExpression expr) (typeOfExpression target)) (analyzeFail "ill-formed assignment statement")
--   return [node {children = [target, expr]}]

normalizeStmtContent :: SyntaxNode c -> AnalysisResult c [SyntaxNode c]
normalizeStmtContent (Node (Pragma ctnt _) [] _) = analyzeFail "\"pragma\" statements not supported"
normalizeStmtContent (Node AliasDeclStmt (ident : exprs) _) = analyzeFail "\"alias\" not supported"
normalizeStmtContent (Node (AssignmentStmt op) [target, expr] _) = do
  newExpr <- toDecoratedExpr expr
  newTarget <- toDecoratedExpr target
  ctx <- newContext
  return $ Just (ctx, AssignmentStmt newTarget newExpr)
normalizeStmtContent (Node BarrierStmt gateOperands _) = do
  newGateExprs <- mapM toDecoratedExpr gateOperands
  ctx <- newContext
  return $ Just (ctx, BarrierStmt newGateExprs)
normalizeStmtContent (Node BoxStmt [time, stmts] _) = analyzeFail "TODO"
normalizeStmtContent (Node BreakStmt [] _) = trivialStatement BreakStmt
normalizeStmtContent (Node (CalStmt calBlock) [] _) = analyzeFail "\"cal\" not supported"
normalizeStmtContent (Node (DefcalgrammarStmt _ cgname) [] _) = analyzeFail "\"defcalgrammar\" not supported"
normalizeStmtContent (Node ClassicalDeclStmt [anyType, ident, maybeExpr] _) =
  toStatementClassicalDecl NilIoMod anyType ident maybeExpr
normalizeStmtContent (Node ConstDeclStmt [sclrType, ident, maybeExpr] _) = analyzeFail "TODO"
normalizeStmtContent (Node ContinueStmt [] _) = trivialStatement ContinueStmt
normalizeStmtContent (Node DefStmt [ident, argDefs, returnType, stmts] _) = analyzeFail "TODO"
normalizeStmtContent (Node DelayStmt (designator : gateOperands) _) = analyzeFail "TODO"
normalizeStmtContent (Node DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  analyzeFail "\"defcal\" not supported"
normalizeStmtContent (Node EndStmt [] _) = trivialStatement EndStmt
normalizeStmtContent (Node ExpressionStmt [expr] _) = do
  exprCtx <- newContext
  ctx <- newContext
  newExpr <- toDecoratedExpr expr
  return $ Just (ctx, ExpressionStmt newExpr)
normalizeStmtContent (Node ExternStmt [ident, paramTypes, returnType] _) =
  analyzeFail "Extern not supported"
normalizeStmtContent (Node ForStmt [declType, ident, condExpr, loopStmt] _) = do
  newDeclType <- toType declType
  newIdent <- toIdentifier ident
  newCondExpr <- toDecoratedExpr condExpr
  loopStmts <- catMaybes <$> toBlock loopStmt
  ctx <- newContext
  return $ Just (ctx, ForStmt newDeclType newIdent newCondExpr loopStmts)
normalizeStmtContent (Node GateStmt [ident, params, args, stmts] _) = analyzeFail "TODO"
normalizeStmtContent (Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) = analyzeFail "TODO"
normalizeStmtContent (Node IfStmt [condExpr, thenBlock, maybeElseBlock] _) = do
  newCondExpr <- toDecoratedExpr condExpr
  thenStmts <- catMaybes <$> toBlock thenBlock
  elseStmts <- catMaybes <$> toBlock maybeElseBlock
  ctx <- newContext
  return $ Just (ctx, IfStmt newCondExpr thenStmts elseStmts)
normalizeStmtContent (Node (IncludeStmt _ tok) [] _) =
  trace "includes must be resolved before analysis" undefined
normalizeStmtContent (Node InputIoDeclStmt [anyType, ident] _) =
  toStatementClassicalDecl InputIoMod anyType ident NilNode
normalizeStmtContent (Node OutputIoDeclStmt [anyType, ident] _) =
  toStatementClassicalDecl OutputIoMod anyType ident NilNode
normalizeStmtContent (Node MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) = analyzeFail "TODO"
normalizeStmtContent (Node CregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- toExpression maybeSize
  let declType = BitType newSize
  newIdent <- toIdentifier ident
  ctx <- newContext
  return $ Just (ctx, ClassicalDeclStmt NilIoMod declType newIdent (nilContext, NilExpr))
normalizeStmtContent (Node QregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- toExpression maybeSize
  let declType = QubitType newSize
  newIdent <- toIdentifier ident
  ctx <- newContext
  return $ Just (ctx, QuantumDeclStmt declType newIdent)
normalizeStmtContent (Node QuantumDeclStmt [qubitType, ident] _) = do
  newQubitType <- toType qubitType
  newIdent <- toIdentifier ident
  ctx <- newContext
  return $ Just (ctx, QuantumDeclStmt newQubitType newIdent)
normalizeStmtContent (Node ResetStmt [gateOp] _) = analyzeFail "TODO"
normalizeStmtContent (Node ReturnStmt [maybeExpr] _) = do
  newMaybeExpr <- toDecoratedExpr maybeExpr
  ctx <- newContext
  return $ Just (ctx, ReturnStmt newMaybeExpr)
normalizeStmtContent (Node WhileStmt [condExpr, loopBlock] _) = do
  newCondExpr <- toDecoratedExpr condExpr
  loopStmts <- catMaybes <$> toBlock loopBlock
  ctx <- newContext
  return $ Just (ctx, WhileStmt newCondExpr loopStmts)
normalizeStmtContent node = trace ("Missing pattern for normalizeStmtContent: " ++ pretty node) undefined

toStatementClassicalDecl :: IoModifier -> SyntaxNode c -> SyntaxNode c -> SyntaxNode c -> AnalysisResult c (Maybe DecoratedStmt)
toStatementClassicalDecl ioMod typeNode identNode maybeInitNode = do
  newType <- toType typeNode
  newIdent <- toIdentifier identNode
  newInit <- toDecoratedExpr maybeInitNode
  unless (isNilNode maybeInitNode) (expectClassicalExpr newType (snd newInit))
  ctx <- newContext
  return $ Just (ctx, ClassicalDeclStmt ioMod newType newIdent newInit)

expectClassicalExpr :: TypeSpec -> Expression -> AnalysisResult c ()
expectClassicalExpr targetType expr = do
  exprType <- computeExpressionType expr
  expectValidImplicitConversion exprType targetType

expectValidImplicitConversion exprType targetType =
  unless
    (isValidImplicitConversion exprType targetType)
    (analyzeFail $ "Invalid implicit conversion from " ++ prettyType exprType ++ " to " ++ prettyType targetType)

isValidImplicitConversion :: TypeSpec -> TypeSpec -> Bool
isValidImplicitConversion exprType targetType = True -- TODO implement

prettyType :: TypeSpec -> String
prettyType = show -- TODO actually pretty-print for errors

computeExpressionType :: Expression -> AnalysisResult c TypeSpec
computeExpressionType expr = return NilType -- TODO implement

trivialStatement :: Statement -> StateT (Analysis c) (Chatty.Chatty String String) (Maybe (Context, Statement))
trivialStatement stmt = do
  ctx <- newContext
  lift (return $ Just (ctx, stmt))

toBlock :: SyntaxNode c -> AnalysisResult c [Maybe (Context, Statement)]
toBlock (Node Scope stmts _) = mapM normalizeStmtContent stmts
toBlock stmt = sequence [normalizeStmtContent stmt]

toIdentifier :: SyntaxNode c -> AnalysisResult c ID
toIdentifier ident = analyzeFail "TODO" -- TODO

toConstantValue :: SyntaxNode c -> AnalysisResult c ConstantValue
toConstantValue constVal = analyzeFail "TODO" -- TODO

toDecoratedExpr :: SyntaxNode c -> AnalysisResult c (Context, Expression)
toDecoratedExpr exprNode = do
  newExpr <- toExpression exprNode
  ctx <- newContext
  return (ctx, newExpr)

toExpression :: SyntaxNode c -> AnalysisResult c Expression
toExpression NilNode = return NilExpr
toExpression (Node ParenExpr [expr] _) = toExpression expr
toExpression (Node IndexExpr [expr, index] _) = analyzeFail "TODO" -- TODO
toExpression (Node (UnaryOperatorExpr op) [expr] _) = analyzeFail "TODO" -- TODO
toExpression (Node (BinaryOperatorExpr op) [left, right] _) = analyzeFail "TODO" -- TODO
toExpression (Node CastExpr [anyType, expr] _) = analyzeFail "TODO" -- TODO
toExpression (Node DurationOfExpr stmts _) = analyzeFail "TODO" -- TODO
toExpression (Node CallExpr (ident : exprs) _) = analyzeFail "TODO" -- TODO
toExpression (Node (Identifier _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (IntegerLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (FloatLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (ImaginaryLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (BooleanLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (BitstringLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (TimingLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node (HardwareQubit _ tok) [] _) = analyzeFail "TODO" -- TODO
toExpression (Node ArrayInitExpr elems _) = analyzeFail "TODO" -- TODO
toExpression (Node SetInitExpr elems _) = analyzeFail "TODO" -- TODO
toExpression (Node RangeInitExpr [begin, step, end] _) = analyzeFail "TODO" -- TODO
toExpression (Node DimExpr [size] _) = analyzeFail "TODO" -- TODO
toExpression (Node MeasureExpr [gateOp] _) = analyzeFail "TODO" -- TODO
toExpression (Node IndexedIdentifier [ident, index] _) = analyzeFail "TODO" -- TODO

toGateModifier :: SyntaxNode c -> AnalysisResult c GateModifier
toGateModifier (Node InvGateModifier [] _) = return InvGateMod
toGateModifier (Node PowGateModifier [expr] _) =
  PowGateMod <$> toExpression expr
toGateModifier (Node CtrlGateModifier [maybeExpr] _) =
  CtrlGateMod <$> toExpression maybeExpr
toGateModifier (Node NegCtrlGateModifier [maybeExpr] _) =
  NegCtrlGateMod <$> toExpression maybeExpr

toType :: SyntaxNode c -> AnalysisResult c TypeSpec
toType NilNode = return NilType
toType (Node BitTypeSpec [maybeSize] _) =
  BitType <$> toExpression maybeSize
toType (Node CregTypeSpec [maybeSize] _) =
  BitType <$> toExpression maybeSize
toType (Node QregTypeSpec [maybeSize] _) =
  QubitType <$> toExpression maybeSize
toType (Node IntTypeSpec [maybeSize] _) =
  IntType <$> toExpression maybeSize
toType (Node UintTypeSpec [maybeSize] _) =
  UintType <$> toExpression maybeSize
toType (Node FloatTypeSpec [maybeSize] _) =
  FloatType <$> toExpression maybeSize
toType (Node AngleTypeSpec [maybeSize] _) =
  AngleType <$> toExpression maybeSize
toType (Node BoolTypeSpec [] _) = return BoolType
toType (Node DurationTypeSpec [] _) = return DurationType
toType (Node StretchTypeSpec [] _) = return StretchType
toType (Node ComplexTypeSpec [maybeSclr] _) =
  ComplexType <$> toType maybeSclr
toType (Node QubitTypeSpec [maybeSize] _) =
  QubitType <$> toExpression maybeSize
toType (Node ArrayTypeSpec (sclrType : exprs) _) = do
  baseType <- toType sclrType
  recurseArrayDimensions baseType exprs
  where
    recurseArrayDimensions :: TypeSpec -> [SyntaxNode c] -> AnalysisResult c TypeSpec
    recurseArrayDimensions innerType [] = return innerType
    recurseArrayDimensions innerType (dimExpr : dimExprs) = do
      newDimExpr <- toExpression dimExpr
      recurseArrayDimensions (ArrayType innerType newDimExpr) dimExprs
toType (Node ReadonlyArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- toType sclrType
  dimCount <- toExpression dimExpr
  return $ ArrayRefType False baseType dimCount
toType (Node MutableArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- toType sclrType
  dimCount <- toExpression dimExpr
  return $ ArrayRefType True baseType dimCount
-}