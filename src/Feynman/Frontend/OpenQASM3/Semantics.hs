module Feynman.Frontend.OpenQASM3.Semantics where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Control.Monad.State as State
import Data.Int (Int64)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Word (Word64)
import Debug.Trace
import Feynman.Core
import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import qualified Feynman.Frontend.OpenQASM3.Syntax as Syntax

data Ref = NilRef | Ref Int deriving (Eq, Ord, Read, Show)

data Context = Context {ref :: Ref, symbols :: (Map.Map String Context)} deriving (Eq, Read, Show)

data Program = Program Block deriving (Eq, Read, Show)

type Block = [(Context, Statement)]

data Statement
  = -- AliasDeclarationStmt Type ID {-rvalue|bitconcat-} [Expression]
    ConstDeclarationStmt Type ID {-const-} Expression
  | ClassicalDeclarationStmt IoModifier {-ctype-} Type ID Expression
  | QuantumDeclarationStmt {-qtype-} Type ID
  | AssignmentStmt {-lvalue-} Expression Expression
  | CompoundAssignmentStmt AssignmentOperator {-lvalue-} Expression Expression
  | GateCallStmt [GateModifier {-gate-}] ID [Expression] [Expression]
  | ResetStmt {-qvalue-} Expression
  | BarrierStmt {-qvalue-} [Expression]
  | DelayStmt {-tvalue-} Expression {-qvalue-} Expression
  | BoxStmt ID Block
  | BreakStmt
  | ContinueStmt
  | EndStmt
  | ReturnStmt {-rvalue-} Expression
  | ExpressionStmt Expression
  | IfStmt {-rvalue-} Expression Block Block
  | ForStmt {-ctype-} Type ID {-rvalue-} Expression Block
  | WhileStmt {-rvalue-} Expression Block
  | GateDefinitionStmt ID [(ID, Type)] [ID] Block
  | FunctionDefinitionStmt ID [(ID, Type)] Type Block
  deriving (Eq, Read, Show)

data Expression
  = NilExpr
  | IdentifierExpr ID
  | LiteralExpr Expression
  | IndexExpr {-rvalue|qvalue-} Expression {-bitvalue|arrayvalue|rangevalue|setvalue-} Expression
  | UnaryOperatorExpr UnaryOperator {-rvalue-} Expression
  | BinaryOperatorExpr
      BinaryOperator
      {-rvalue-} Expression
      {-rvalue-} Expression
  | CastExpr {-ctype-} Type {-rvalue-} Expression
  | DurationOfExpr Block
  | CallExpr ID {-rvalue-} [Expression]
  | ArrayInitExpr {-rvalue|arrayvalue-} [Expression]
  | SetInitExpr {-rvalue-} [Expression]
  | RangeInitExpr
      {-rvalue-} Expression
      {-rvalue?-} Expression
      {-rvalue-} Expression
  | MeasureExpr {-qvalue-} [Expression]
  deriving (Eq, Read, Show)

data Type
  = NilType
  | BitType Expression -- size
  | IntType Expression -- size
  | UintType Expression -- size
  | FloatType Expression -- size
  | AngleType Expression -- size
  | BoolType
  | DurationType
  | StretchType
  | ComplexType Type -- base
  | QubitType Expression -- size
  | HwQubitType Int -- hwindex
  | ArrayType Type Expression -- base, size
  | ArrayRefType Bool Type Expression -- mutable, base, dim
  deriving (Eq, Read, Show)

data AssignmentOperator
  = PlusAsgn
  | MinusAsgn
  | AsteriskAsgn
  | SlashAsgn
  | AmpersandAsgn
  | PipeAsgn
  | TildeAsgn
  | CaretAsgn
  | DoubleLessAsgn
  | DoubleGreaterAsgn
  | PercentAsgn
  | DoubleAsteriskAsgn
  deriving (Eq, Read, Show)

data BinaryOperator
  = PlusBinop
  | DoublePlusBinop
  | MinusBinop
  | AsteriskBinop
  | DoubleAsteriskBinop
  | SlashBinop
  | PercentBinop
  | PipeBinop
  | DoublePipeBinop
  | AmpersandBinop
  | DoubleAmpersandBinop
  | CaretBinop
  | DoubleLessBinop
  | DoubleGreaterBinop
  | DoubleEqualsBinop
  | ExclamationPointEqualsBinop
  | LessBinop
  | GreaterBinop
  | LessEqualsBinop
  | GreaterEqualsBinop
  deriving (Eq, Read, Show)

data UnaryOperator
  = MinusUnop
  | TildeUnop
  | ExclamationPointUnop
  deriving (Eq, Read, Show)

data IoModifier
  = NilIoMod
  | InputIoMod
  | OutputIoMod
  deriving (Eq, Read, Show)

data GateModifier
  = NilGateMod
  | InvGateMod
  | PowGateMod Expression
  | CtrlGateMod Expression
  | NegCtrlGateMod Expression
  deriving (Eq, Read, Show)

data ConstantValue
  = NilValue
  | BitValue Int Int64
  | IntValue Int Int64
  | UintValue Int Word64
  | FloatValue Int Double
  | AngleValue Int Double
  | BoolValue Bool
  | DurationValue Bool Double
  | ComplexValue Int Double Double
  | ArrayValue [ConstantValue]
  deriving (Eq, Read, Show)

{-
-- Reducing duration expressions is nontrivial
data Duration
  = ZeroDuration
  | ExactDtDuration Double
  | ExactNsDuration Double
  | StretchDuration
  | SumDuration [Duration]
  | MaxDuration [Duration]
  deriving (Eq, Read, Show)

-- coerceToCompatible
-- coerceToIntegral

typeOfValue :: ConstantValue -> ScalarType
typeOfValue (BitValue bits _) = BitType $ LiteralParam bits
typeOfValue (IntValue bits _) = IntType $ LiteralParam bits
typeOfValue (UintValue bits _) = UintType $ LiteralParam bits
typeOfValue (FloatValue bits _) = FloatType $ LiteralParam bits
typeOfValue (AngleValue bits _) = AngleType $ LiteralParam bits
typeOfValue (BoolValue _) = BoolType
typeOfValue (DurationValue stretch _) = DurationType $ LiteralParam stretch
typeOfValue (ComplexValue bits realPart imagPart) = ComplexType $ LiteralParam bits

-- typeOfValue (ArrayValue elT dims _) = ArrayType {elementType = baseType, sizes = sizes}

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

-}

data Analysis c = Analysis {nextRef :: Int, nextSymbols :: Map.Map String Context, sources :: Map.Map Ref c}

type Result c v = StateT (Analysis c) (Chatty.Chatty String String) v

freshAnalysis :: Analysis c
freshAnalysis = Analysis 1 Map.empty Map.empty

analyze :: Ast.Node Syntax.Tag c -> Chatty.Chatty String String (Program, Analysis c)
analyze (Ast.Node (Syntax.Program _ _ tok) stmts _) =
  evalStateT
    ( do
        statements <- mapM analyzeStatementAnnotations stmts
        analysis <- get
        return (Program (catMaybes statements), analysis)
    )
    freshAnalysis

newContext :: StateT (Analysis c) (Chatty.Chatty String String) Context
newContext = do
  Analysis {nextRef = n, nextSymbols = syms} <- get
  modify (\s -> s {nextRef = n + 1})
  return $ Context {ref = Ref n, symbols = syms}

analyzeFail :: String -> Result c d
analyzeFail = lift . Chatty.fail

analyzeStatementAnnotations :: Ast.Node Syntax.Tag c -> Result c (Maybe (Context, Statement))
analyzeStatementAnnotations (Ast.Node Syntax.Statement [] _) = trace "Empty statement" undefined
analyzeStatementAnnotations (Ast.Node Syntax.Statement [content] ctx) = analyzeStatement content
analyzeStatementAnnotations (Ast.Node Syntax.Statement (_ : _) _) = analyzeFail "Annotations not supported"

analyzeStatement :: Ast.Node Syntax.Tag c -> Result c (Maybe (Context, Statement))
analyzeStatement (Ast.Node (Syntax.Pragma ctnt _) [] _) = analyzeFail "\"pragma\" statements not supported"
analyzeStatement (Ast.Node Syntax.AliasDeclStmt (ident : exprs) _) = analyzeFail "\"alias\" not supported"
analyzeStatement (Ast.Node (Syntax.AssignmentStmt op) [target, expr] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.BarrierStmt gateOperands _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.BoxStmt [time, stmts] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.BreakStmt [] _) = trivialStatement BreakStmt
analyzeStatement (Ast.Node (Syntax.CalStmt calBlock) [] _) = analyzeFail "\"cal\" not supported"
analyzeStatement (Ast.Node (Syntax.DefcalgrammarStmt _ cgname) [] _) = analyzeFail "\"defcalgrammar\" not supported"
analyzeStatement (Ast.Node Syntax.ClassicalDeclStmt [anyType, ident, maybeExpr] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.ConstDeclStmt [sclrType, ident, maybeExpr] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.ContinueStmt [] _) = trivialStatement ContinueStmt
analyzeStatement (Ast.Node Syntax.DefStmt [ident, argDefs, returnType, stmts] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.DelayStmt (designator : gateOperands) _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  analyzeFail "\"defcal\" not supported"
analyzeStatement (Ast.Node Syntax.EndStmt [] _) = trivialStatement EndStmt
analyzeStatement (Ast.Node Syntax.ExpressionStmt [expr] _) = do
  ctx <- newContext
  newExpr <- analyzeExpression expr
  return $ Just (ctx, ExpressionStmt newExpr)
analyzeStatement (Ast.Node Syntax.ExternStmt [ident, paramTypes, returnType] _) =
  analyzeFail "Extern not supported"
analyzeStatement (Ast.Node Syntax.ForStmt [declType, ident, condExpr, loopStmt] _) = do
  ctx <- newContext
  newDeclType <- analyzeExpressionType declType
  newIdent <- analyzeIdentifier ident
  newCondExpr <- analyzeExpression condExpr
  loopStmts <- catMaybes <$> analyzeBlock loopStmt
  return $ Just (ctx, ForStmt newDeclType newIdent newCondExpr loopStmts)
analyzeStatement (Ast.Node Syntax.GateStmt [ident, params, args, stmts] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.IfStmt [condExpr, thenBlock, maybeElseBlock] _) = do
  ctx <- newContext
  newCondExpr <- analyzeExpression condExpr
  thenStmts <- catMaybes <$> analyzeBlock thenBlock
  elseStmts <- catMaybes <$> analyzeBlock maybeElseBlock
  return $ Just (ctx, IfStmt newCondExpr thenStmts elseStmts)
analyzeStatement (Ast.Node (Syntax.IncludeStmt _ tok) [] _) =
  trace "includes must be resolved before analysis" undefined
analyzeStatement (Ast.Node Syntax.InputIoDeclStmt [anyType, ident] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.OutputIoDeclStmt [anyType, ident] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.CregOldStyleDeclStmt [ident, maybeSize] _) = do
  ctx <- newContext
  newSize <- analyzeExpression maybeSize
  let declType = BitType newSize
  newIdent <- analyzeIdentifier ident
  return $ Just (ctx, ClassicalDeclarationStmt NilIoMod declType newIdent NilExpr)
analyzeStatement (Ast.Node Syntax.QregOldStyleDeclStmt [ident, maybeSize] _) = do
  ctx <- newContext
  newSize <- analyzeExpression maybeSize
  let declType = QubitType newSize
  newIdent <- analyzeIdentifier ident
  return $ Just (ctx, QuantumDeclarationStmt declType newIdent)
analyzeStatement (Ast.Node Syntax.QuantumDeclStmt [qubitType, ident] _) = do
  ctx <- newContext
  newQubitType <- analyzeExpressionType qubitType
  newIdent <- analyzeIdentifier ident
  return $ Just (ctx, QuantumDeclarationStmt newQubitType newIdent)
analyzeStatement (Ast.Node Syntax.ResetStmt [gateOp] _) = analyzeFail "TODO"
analyzeStatement (Ast.Node Syntax.ReturnStmt [maybeExpr] _) = do
  ctx <- newContext
  newMaybeExpr <- analyzeExpression maybeExpr
  return $ Just (ctx, ReturnStmt newMaybeExpr)
analyzeStatement (Ast.Node Syntax.WhileStmt [condExpr, loopBlock] _) = do
  ctx <- newContext
  newCondExpr <- analyzeExpression condExpr
  loopStmts <- catMaybes <$> analyzeBlock loopBlock
  return $ Just (ctx, WhileStmt newCondExpr loopStmts)
analyzeStatement node = trace ("Missing pattern for analyzeStatement: " ++ Syntax.pretty node) undefined

trivialStatement :: Statement -> StateT (Analysis c) (Chatty.Chatty String String) (Maybe (Context, Statement))
trivialStatement stmt = do
  ctx <- newContext
  lift (return $ Just (ctx, stmt))

analyzeBlock :: Ast.Node Syntax.Tag c -> Result c [Maybe (Context, Statement)]
analyzeBlock (Ast.Node Syntax.Scope stmts _) = mapM analyzeStatement stmts
analyzeBlock stmt = sequence [analyzeStatement stmt]

analyzeIdentifier :: Ast.Node Syntax.Tag c -> Result c ID
analyzeIdentifier ident = analyzeFail "TODO" -- TODO

analyzeConstantValue :: Ast.Node Syntax.Tag c -> Result c ConstantValue
analyzeConstantValue constVal = analyzeFail "TODO" -- TODO

analyzeExpression :: Ast.Node Syntax.Tag c -> Result c Expression
analyzeExpression Ast.NilNode = return NilExpr
analyzeExpression (Ast.Node Syntax.ParenExpr [expr] _) = analyzeExpression expr
analyzeExpression (Ast.Node Syntax.IndexExpr [expr, index] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.UnaryOperatorExpr op) [expr] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BinaryOperatorExpr op) [left, right] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.CastExpr [anyType, expr] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.DurationOfExpr stmts _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.CallExpr (ident : exprs) _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.Identifier _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.IntegerLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.FloatLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.ImaginaryLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BooleanLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BitstringLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.TimingLiteral _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.HardwareQubit _ tok) [] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.ArrayInitExpr elems _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.SetInitExpr elems _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.RangeInitExpr [begin, step, end] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.DimExpr [size] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.MeasureExpr [gateOp] _) = analyzeFail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.IndexedIdentifier [ident, index] _) = analyzeFail "TODO" -- TODO

analyzeGateModifier :: Ast.Node Syntax.Tag c -> Result c GateModifier
analyzeGateModifier (Ast.Node Syntax.InvGateModifier [] _) = return InvGateMod
analyzeGateModifier (Ast.Node Syntax.PowGateModifier [expr] _) =
  PowGateMod <$> analyzeExpression expr
analyzeGateModifier (Ast.Node Syntax.CtrlGateModifier [maybeExpr] _) =
  CtrlGateMod <$> analyzeExpression maybeExpr
analyzeGateModifier (Ast.Node Syntax.NegCtrlGateModifier [maybeExpr] _) =
  NegCtrlGateMod <$> analyzeExpression maybeExpr

analyzeExpressionType :: Ast.Node Syntax.Tag c -> Result c Type
analyzeExpressionType Ast.NilNode = return NilType
analyzeExpressionType (Ast.Node Syntax.BitTypeSpec [maybeSize] _) =
  BitType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.CregTypeSpec [maybeSize] _) =
  BitType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.QregTypeSpec [maybeSize] _) =
  QubitType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.IntTypeSpec [maybeSize] _) =
  IntType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.UintTypeSpec [maybeSize] _) =
  UintType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.FloatTypeSpec [maybeSize] _) =
  FloatType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.AngleTypeSpec [maybeSize] _) =
  AngleType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.BoolTypeSpec [] _) = return BoolType
analyzeExpressionType (Ast.Node Syntax.DurationTypeSpec [] _) = return DurationType
analyzeExpressionType (Ast.Node Syntax.StretchTypeSpec [] _) = return StretchType
analyzeExpressionType (Ast.Node Syntax.ComplexTypeSpec [maybeSclr] _) =
  ComplexType <$> analyzeExpressionType maybeSclr
analyzeExpressionType (Ast.Node Syntax.QubitTypeSpec [maybeSize] _) =
  QubitType <$> analyzeExpression maybeSize
analyzeExpressionType (Ast.Node Syntax.ArrayTypeSpec (sclrType : exprs) _) = do
  baseType <- analyzeExpressionType sclrType
  recurseArrayDimensions baseType exprs
  where
    recurseArrayDimensions :: Type -> [Ast.Node Syntax.Tag c] -> Result c Type
    recurseArrayDimensions innerType [] = return innerType
    recurseArrayDimensions innerType (dimExpr : dimExprs) = do
      newDimExpr <- analyzeExpression dimExpr
      recurseArrayDimensions (ArrayType innerType newDimExpr) dimExprs
analyzeExpressionType (Ast.Node Syntax.ReadonlyArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- analyzeExpressionType sclrType
  dimCount <- analyzeExpression dimExpr
  return $ ArrayRefType False baseType dimCount
analyzeExpressionType (Ast.Node Syntax.MutableArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- analyzeExpressionType sclrType
  dimCount <- analyzeExpression dimExpr
  return $ ArrayRefType True baseType dimCount
