module Feynman.Frontend.OpenQASM3.Semantics where

import Control.Monad
import Control.Monad.State (runState)
import qualified Control.Monad.State as State
import Data.Int (Int64)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Word (Word64)
import Debug.Trace
import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import qualified Feynman.Frontend.OpenQASM3.Syntax as Syntax

data Ref = NilRef | Ref Int deriving (Eq, Ord, Read, Show)

data IdentifierAttributes = IdentifierAttributes
  { identName :: String,
    identRef :: Ref,
    identScopeRef :: Ref
    -- identType :: ExpressionType,
    -- identValue :: ConstantValue
  }
  deriving (Eq, Read, Show)

initialIdentifierAttributes :: IdentifierAttributes
initialIdentifierAttributes =
  IdentifierAttributes
    { identName = "",
      identRef = NilRef,
      identScopeRef = NilRef
      -- identType = NilType,
      -- identValue = NilValue
    }

-- data TypeParameter a = LiteralParam a | VariableParam Ref
--   deriving (Eq, Ord, Read, Show)

-- data ConstantValue
--   = NilValue
--   | IntValue Int
--   | TupleValue [ConstantValue]
--   deriving (Eq, Read, Show)

-- expressionTypeFromNode :: p -> ExpressionType
-- expressionTypeFromNode node = NilType -- TODO

data SemanticGraph = SemanticGraph
  { semGraphProgram :: Program,
    semGraphScopes :: Map.Map Ref LexicalScope,
    semGraphIdentifiers :: Map.Map Ref IdentifierAttributes
    -- semGraphExpressions :: Map.Map Ref SemanticNode,
    -- semGraphTypes :: Map.Map Ref ExpressionType,
    -- semGraphValues :: Map.Map Ref ConstantValue,
  }
  deriving (Eq, Read, Show)

initialSemanticGraph :: SemanticGraph
initialSemanticGraph =
  SemanticGraph
    { semGraphProgram = Program [],
      semGraphScopes = Map.empty,
      semGraphIdentifiers = Map.empty
      -- semGraphExpressions = Map.empty,
      -- semGraphTypes = Map.empty,
      -- semGraphValues = Map.empty
    }

data LexicalScope = LexicalScope
  { lexScopeParentRef :: Ref,
    lexScopeIdentifiers :: Map.Map String IdentifierAttributes
  }
  deriving (Eq, Read, Show)

initialLexicalScope :: LexicalScope
initialLexicalScope = LexicalScope NilRef Map.empty

data Program = Program [Statement] deriving (Eq, Read, Show)

data Statement
  = -- AliasDeclarationStmt ExpressionType Identifier {-rvalue|bitconcat-} [Expression]
    ConstDeclarationStmt ExpressionType Identifier {-const-} Expression
  | ClassicalDeclarationStmt IoModifier {-ctype-} ExpressionType Identifier Expression
  | QuantumDeclarationStmt {-qtype-} ExpressionType Identifier
  | AssignmentStmt {-lvalue-} Expression Expression
  | CompoundAssignmentStmt AssignmentOperator {-lvalue-} Expression Expression
  | GateCallStmt Identifier [Expression] [Expression] -- [modifiers::List<GateModifier>, target::Identifier, params::List<Expression>?, designator::Expression?, args::List<(HardwareQubit | IndexedIdentifier)>?]
  | ResetStmt {-qvalue-} Expression
  | BarrierStmt {-qvalue-} [Expression]
  | DelayStmt {-tvalue-} Expression {-qvalue-} Expression
  | BoxStmt Identifier [Statement]
  | BreakStmt
  | ContinueStmt
  | EndStmt
  | ReturnStmt {-rvalue-} Expression
  | ExpressionStmt Expression
  | IfStmt {-rvalue-} Expression [Statement] [Statement]
  | ForStmt {-ctype-} ExpressionType Identifier {-rvalue-} Expression [Statement]
  | WhileStmt {-rvalue-} Expression [Statement]
  -- \| GateDefinitionStmt Identifier ...
  -- \| FunctionDefinitionStmt Identifier ...
  deriving (Eq, Read, Show)

data Identifier = Identifier Ref String deriving (Eq, Read, Show)

data Expression
  = NilExpr
  | IdentifierExpr Ref
  | LiteralExpr ConstantValue
  | IndexExpr {-rvalue|qvalue-} Expression {-bitvalue|arrayvalue|rangevalue|setvalue-} Expression
  | UnaryOperatorExpr UnaryOperator {-rvalue-} Expression
  | BinaryOperatorExpr
      BinaryOperator
      {-rvalue-} Expression
      {-rvalue-} Expression
  | CastExpr {-ctype-} ExpressionType {-rvalue-} Expression
  | DurationOfExpr [Statement]
  | CallExpr Ref {-rvalue-} [Expression]
  | ArrayInitExpr {-rvalue|arrayvalue-} [Expression]
  | SetInitExpr {-rvalue-} [Expression]
  | RangeInitExpr
      {-rvalue-} Expression
      {-rvalue?-} Expression
      {-rvalue-} Expression
  | MeasureExpr {-qvalue-} [Expression]
  deriving (Eq, Read, Show)

data ExpressionType
  = NilType
  | BitType Expression -- size
  | IntType Expression -- size
  | UintType Expression -- size
  | FloatType Expression -- size
  | AngleType Expression -- size
  | BoolType
  | DurationType
  | StretchType
  | ComplexType ExpressionType -- base
  | QubitType Expression -- size
  | HwQubitType Int -- hwindex
  | ArrayType ExpressionType Expression -- base, size
  | ArrayRefType Bool ExpressionType Expression -- mutable, base, dim
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

type Result v = Chatty.Chatty String String v

analyze :: Ast.Node Syntax.Tag c -> Result Program
analyze (Ast.Node (Syntax.Program _ _ tok) stmts _) = do
  statements <- sequence (map analyzeStatementAnnotations stmts)
  return $ Program (catMaybes statements)

analyzeStatementAnnotations :: Ast.Node Syntax.Tag c -> Result (Maybe Statement)
analyzeStatementAnnotations (Ast.Node Syntax.Statement [] _) = trace "Empty statement" undefined
analyzeStatementAnnotations (Ast.Node Syntax.Statement [content] ctx) = analyzeStatement content
analyzeStatementAnnotations (Ast.Node Syntax.Statement (_ : _) _) = Chatty.fail "Annotations not supported"

analyzeStatement :: Ast.Node Syntax.Tag c -> Result (Maybe Statement)
analyzeStatement (Ast.Node (Syntax.Pragma ctnt _) [] _) = Chatty.fail "\"pragma\" statements not supported"
analyzeStatement (Ast.Node Syntax.AliasDeclStmt (ident : exprs) _) = Chatty.fail "\"alias\" not supported"
analyzeStatement (Ast.Node (Syntax.AssignmentStmt op) [target, expr] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.BarrierStmt gateOperands _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.BoxStmt [time, stmts] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.BreakStmt [] _) = return $ Just BreakStmt
analyzeStatement (Ast.Node (Syntax.CalStmt calBlock) [] _) = Chatty.fail "\"cal\" not supported"
analyzeStatement (Ast.Node (Syntax.DefcalgrammarStmt _ cgname) [] _) = Chatty.fail "\"defcalgrammar\" not supported"
analyzeStatement (Ast.Node Syntax.ClassicalDeclStmt [anyType, ident, maybeExpr] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.ConstDeclStmt [sclrType, ident, maybeExpr] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.ContinueStmt [] _) = return $ Just ContinueStmt
analyzeStatement (Ast.Node Syntax.DefStmt [ident, argDefs, returnType, stmts] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.DelayStmt (designator : gateOperands) _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  Chatty.fail "\"defcal\" not supported"
analyzeStatement (Ast.Node Syntax.EndStmt [] _) = return $ Just EndStmt
analyzeStatement (Ast.Node Syntax.ExpressionStmt [expr] _) =
  Just . ExpressionStmt <$> analyzeExpression expr
analyzeStatement (Ast.Node Syntax.ExternStmt [ident, paramTypes, returnType] _) =
  Chatty.fail "Extern not supported"
analyzeStatement (Ast.Node Syntax.ForStmt [declType, ident, condExpr, loopStmt] _) = do
  newDeclType <- analyzeExpressionType declType
  newIdent <- analyzeIdentifier ident
  newCondExpr <- analyzeExpression condExpr
  loopStmts <- catMaybes <$> analyzeBlock loopStmt
  return $ Just $ ForStmt newDeclType newIdent newCondExpr loopStmts
analyzeStatement (Ast.Node Syntax.GateStmt [ident, params, args, stmts] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.IfStmt [condExpr, thenBlock, maybeElseBlock] _) = do
  newCondExpr <- analyzeExpression condExpr
  thenStmts <- catMaybes <$> analyzeBlock thenBlock
  elseStmts <- catMaybes <$> analyzeBlock maybeElseBlock
  return $ Just $ IfStmt newCondExpr thenStmts elseStmts
analyzeStatement (Ast.Node (Syntax.IncludeStmt _ tok) [] _) =
  trace "includes must be resolved before analysis" undefined
analyzeStatement (Ast.Node Syntax.InputIoDeclStmt [anyType, ident] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.OutputIoDeclStmt [anyType, ident] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.CregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- analyzeExpression maybeSize
  let declType = BitType newSize
  newIdent <- analyzeIdentifier ident
  return $ Just $ ClassicalDeclarationStmt NilIoMod declType newIdent NilExpr
analyzeStatement (Ast.Node Syntax.QregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- analyzeExpression maybeSize
  let declType = QubitType newSize
  newIdent <- analyzeIdentifier ident
  return $ Just $ QuantumDeclarationStmt declType newIdent
analyzeStatement (Ast.Node Syntax.QuantumDeclStmt [qubitType, ident] _) = do
  newQubitType <- analyzeExpressionType qubitType
  newIdent <- analyzeIdentifier ident
  return $ Just $ QuantumDeclarationStmt newQubitType newIdent
analyzeStatement (Ast.Node Syntax.ResetStmt [gateOp] _) = Chatty.fail "TODO"
analyzeStatement (Ast.Node Syntax.ReturnStmt [maybeExpr] _) =
  Just . ReturnStmt <$> analyzeExpression maybeExpr
analyzeStatement (Ast.Node Syntax.WhileStmt [condExpr, loopBlock] _) = do
  newCondExpr <- analyzeExpression condExpr
  loopStmts <- catMaybes <$> analyzeBlock loopBlock
  return $ Just $ WhileStmt newCondExpr loopStmts
analyzeStatement node = trace ("Missing pattern for analyzeStatement: " ++ Syntax.pretty node) undefined

analyzeBlock :: Ast.Node Syntax.Tag c -> Result [Maybe Statement]
analyzeBlock (Ast.Node Syntax.Scope stmts _) = mapM analyzeStatement stmts
analyzeBlock stmt = sequence [analyzeStatement stmt]

analyzeIdentifier :: Ast.Node Syntax.Tag c -> Result Identifier
analyzeIdentifier ident = Chatty.fail "TODO" -- TODO

analyzeConstantValue :: Ast.Node Syntax.Tag c -> Result ConstantValue
analyzeConstantValue constVal = Chatty.fail "TODO" -- TODO

analyzeExpression :: Ast.Node Syntax.Tag c -> Result Expression
analyzeExpression Ast.NilNode = return NilExpr
analyzeExpression (Ast.Node Syntax.ParenExpr [expr] _) = analyzeExpression expr
analyzeExpression (Ast.Node Syntax.IndexExpr [expr, index] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.UnaryOperatorExpr op) [expr] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BinaryOperatorExpr op) [left, right] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.CastExpr [anyType, expr] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.DurationOfExpr stmts _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.CallExpr (ident : exprs) _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.Identifier _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.IntegerLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.FloatLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.ImaginaryLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BooleanLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.BitstringLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.TimingLiteral _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node (Syntax.HardwareQubit _ tok) [] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.ArrayInitExpr elems _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.SetInitExpr elems _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.RangeInitExpr [begin, step, end] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.DimExpr [size] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.MeasureExpr [gateOp] _) = Chatty.fail "TODO" -- TODO
analyzeExpression (Ast.Node Syntax.IndexedIdentifier [ident, index] _) = Chatty.fail "TODO" -- TODO

analyzeGateModifier :: Ast.Node Syntax.Tag c -> Result GateModifier
analyzeGateModifier (Ast.Node Syntax.InvGateModifier [] _) = return InvGateMod
analyzeGateModifier (Ast.Node Syntax.PowGateModifier [expr] _) =
  PowGateMod <$> analyzeExpression expr
analyzeGateModifier (Ast.Node Syntax.CtrlGateModifier [maybeExpr] _) =
  CtrlGateMod <$> analyzeExpression maybeExpr
analyzeGateModifier (Ast.Node Syntax.NegCtrlGateModifier [maybeExpr] _) =
  NegCtrlGateMod <$> analyzeExpression maybeExpr

analyzeExpressionType :: Ast.Node Syntax.Tag c -> Result ExpressionType
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
    recurseArrayDimensions :: ExpressionType -> [Ast.Node Syntax.Tag c] -> Result ExpressionType
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
