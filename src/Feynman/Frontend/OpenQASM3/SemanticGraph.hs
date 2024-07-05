module Frontend.OpenQASM3 where

import Ast qualified
import Control.Monad
import Control.Monad.State (runState)
import Control.Monad.State qualified as State
import Data.Data qualified as Ast
import Data.Int (Int64)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Word (Word64)
import Debug.Trace
import Frontend.OpenQASM3.Chatty
import Frontend.OpenQASM3.Result
import Frontend.OpenQASM3.Syntax qualified as Q3

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

newtype Program = Program [Statement] deriving (Eq, Read, Show)

data Statement
  = AliasDeclarationStmt ExpressionType Identifier {-rvalue|bitconcat-} [Expression]
  | ConstDeclarationStmt ExpressionType Identifier {-const-} Expression
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
  deriving
    ( -- | GateDefinitionStmt Identifier ...
      -- | FunctionDefinitionStmt Identifier ...
      Eq,
      Read,
      Show
    )

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

{-
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

semanticGraphFrom :: Q3.SyntaxNode -> Result SemanticGraph
semanticGraphFrom (Ast.Node (Q3.Program _ _ tok) stmts _) =
  (\sgs -> initialSemanticGraph {semGraphProgram = Program sgs}) <$> semanticGraphStatementsFrom stmts

semanticGraphStatementsFrom :: [Q3.SyntaxNode] -> Result [Statement]
semanticGraphStatementsFrom = sequence . mapMaybe (sequence . semanticGraphStatementFrom)

semanticGraphStatementFrom :: Q3.SyntaxNode -> Result (Maybe Statement)
semanticGraphStatementFrom (Ast.Node (Q3.Pragma ctnt _) [] _) = failResult "Pragma statements not supported"
semanticGraphStatementFrom (Ast.Node Q3.Statement (stmt : annots) _) = semanticGraphStatementFrom stmt
semanticGraphStatementFrom (Ast.Node (Q3.Annotation name ctnt _) [] _) = failResult "Annotations not supported"
semanticGraphStatementFrom (Ast.Node Q3.AliasDeclStmt (ident : exprs) _) = failResult "Aliases not supported"
semanticGraphStatementFrom (Ast.Node (Q3.AssignmentStmt op) [target, expr] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.BarrierStmt gateOperands _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.BoxStmt [time, stmts] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.BreakStmt [] _) = return $ Just BreakStmt
semanticGraphStatementFrom (Ast.Node (Q3.CalStmt calBlock) [] _) = failResult "Cal not supported"
semanticGraphStatementFrom (Ast.Node (Q3.DefcalgrammarStmt _ cgname) [] _) = failResult "Defcalgrammar not supported"
semanticGraphStatementFrom (Ast.Node Q3.ClassicalDeclStmt [anyType, ident, maybeExpr] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.ConstDeclStmt [sclrType, ident, maybeExpr] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.ContinueStmt [] _) = return $ Just ContinueStmt
semanticGraphStatementFrom (Ast.Node Q3.DefStmt [ident, argDefs, returnType, stmts] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.DelayStmt (designator : gateOperands) _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  failResult "Defcal not supported"
semanticGraphStatementFrom (Ast.Node Q3.EndStmt [] _) = return $ Just EndStmt
semanticGraphStatementFrom (Ast.Node Q3.ExpressionStmt [expr] _) =
  Just . ExpressionStmt <$> semanticGraphExpressionFrom expr
semanticGraphStatementFrom (Ast.Node Q3.ExternStmt [ident, paramTypes, returnType] _) =
  failResult "Extern not supported"
semanticGraphStatementFrom (Ast.Node Q3.ForStmt [declType, ident, condExpr, loopStmt] _) = do
  newDeclType <- semanticGraphExpressionTypeFrom declType
  newIdent <- semanticGraphIdentifierFrom ident
  newCondExpr <- semanticGraphExpressionFrom condExpr
  loopStmts <- catMaybes <$> semanticGraphBlockFrom loopStmt
  return $ Just $ ForStmt newDeclType newIdent newCondExpr loopStmts
semanticGraphStatementFrom (Ast.Node Q3.GateStmt [ident, params, args, stmts] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.IfStmt [condExpr, thenBlock, maybeElseBlock] _) = do
  newCondExpr <- semanticGraphExpressionFrom condExpr
  thenStmts <- catMaybes <$> semanticGraphBlockFrom thenBlock
  elseStmts <- catMaybes <$> semanticGraphBlockFrom maybeElseBlock
  return $ Just $ IfStmt newCondExpr thenStmts elseStmts
semanticGraphStatementFrom (Ast.Node (Q3.IncludeStmt _ tok) [] _) =
  trace "includes must be resolved before handling by SemanticGraph" undefined
semanticGraphStatementFrom (Ast.Node Q3.InputIoDeclStmt [anyType, ident] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.OutputIoDeclStmt [anyType, ident] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.CregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- semanticGraphExpressionFrom maybeSize
  let declType = BitType newSize
  newIdent <- semanticGraphIdentifierFrom ident
  return $ Just $ ClassicalDeclarationStmt NilIoMod declType newIdent NilExpr
semanticGraphStatementFrom (Ast.Node Q3.QregOldStyleDeclStmt [ident, maybeSize] _) = do
  newSize <- semanticGraphExpressionFrom maybeSize
  let declType = QubitType newSize
  newIdent <- semanticGraphIdentifierFrom ident
  return $ Just $ QuantumDeclarationStmt declType newIdent
semanticGraphStatementFrom (Ast.Node Q3.QuantumDeclStmt [qubitType, ident] _) = do
  newQubitType <- semanticGraphExpressionTypeFrom qubitType
  newIdent <- semanticGraphIdentifierFrom ident
  return $ Just $ QuantumDeclarationStmt newQubitType newIdent
semanticGraphStatementFrom (Ast.Node Q3.ResetStmt [gateOp] _) = failResult "TODO"
semanticGraphStatementFrom (Ast.Node Q3.ReturnStmt [maybeExpr] _) =
  Just . ReturnStmt <$> semanticGraphExpressionFrom maybeExpr
semanticGraphStatementFrom (Ast.Node Q3.WhileStmt [condExpr, loopBlock] _) = do
  newCondExpr <- semanticGraphExpressionFrom condExpr
  loopStmts <- catMaybes <$> semanticGraphBlockFrom loopBlock
  return $ Just $ WhileStmt newCondExpr loopStmts
semanticGraphStatementFrom node = trace ("Missing pattern for semanticGraphStatementFrom: " ++ show node) undefined

semanticGraphBlockFrom :: Q3.SyntaxNode -> Result [Maybe Statement]
semanticGraphBlockFrom (Ast.Node Q3.Scope stmts _) = mapM semanticGraphStatementFrom stmts
semanticGraphBlockFrom stmt = sequence [semanticGraphStatementFrom stmt]

semanticGraphIdentifierFrom :: Q3.SyntaxNode -> Result Identifier
semanticGraphIdentifierFrom ident = failResult "TODO" -- TODO

semanticGraphConstantValueFrom :: Q3.SyntaxNode -> Result ConstantValue
semanticGraphConstantValueFrom constVal = failResult "TODO" -- TODO

semanticGraphExpressionFrom :: Q3.SyntaxNode -> Result Expression
semanticGraphExpressionFrom Ast.NilNode = return NilExpr
semanticGraphExpressionFrom (Ast.Node Q3.ParenExpr [expr] _) = semanticGraphExpressionFrom expr
semanticGraphExpressionFrom (Ast.Node Q3.IndexExpr [expr, index] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.UnaryOperatorExpr op) [expr] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.BinaryOperatorExpr op) [left, right] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.CastExpr [anyType, expr] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.DurationOfExpr stmts _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.CallExpr (ident : exprs) _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.Identifier _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.IntegerLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.FloatLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.ImaginaryLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.BooleanLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.BitstringLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.TimingLiteral _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node (Q3.HardwareQubit _ tok) [] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.ArrayInitExpr elems _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.SetInitExpr elems _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.RangeInitExpr [begin, step, end] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.DimExpr [size] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.MeasureExpr [gateOp] _) = failResult "TODO" -- TODO
semanticGraphExpressionFrom (Ast.Node Q3.IndexedIdentifier [ident, index] _) = failResult "TODO" -- TODO

semanticGraphGateModifierFrom :: Q3.SyntaxNode -> Result GateModifier
semanticGraphGateModifierFrom (Ast.Node Q3.InvGateModifier [] _) = return InvGateMod
semanticGraphGateModifierFrom (Ast.Node Q3.PowGateModifier [expr] _) =
  PowGateMod <$> semanticGraphExpressionFrom expr
semanticGraphGateModifierFrom (Ast.Node Q3.CtrlGateModifier [maybeExpr] _) =
  CtrlGateMod <$> semanticGraphExpressionFrom maybeExpr
semanticGraphGateModifierFrom (Ast.Node Q3.NegCtrlGateModifier [maybeExpr] _) =
  NegCtrlGateMod <$> semanticGraphExpressionFrom maybeExpr

semanticGraphExpressionTypeFrom :: Q3.SyntaxNode -> Result ExpressionType
semanticGraphExpressionTypeFrom Ast.NilNode = return NilType
semanticGraphExpressionTypeFrom (Ast.Node Q3.BitTypeSpec [maybeSize] _) =
  BitType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.CregTypeSpec [maybeSize] _) =
  BitType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.QregTypeSpec [maybeSize] _) =
  QubitType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.IntTypeSpec [maybeSize] _) =
  IntType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.UintTypeSpec [maybeSize] _) =
  UintType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.FloatTypeSpec [maybeSize] _) =
  FloatType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.AngleTypeSpec [maybeSize] _) =
  AngleType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.BoolTypeSpec [] _) = return BoolType
semanticGraphExpressionTypeFrom (Ast.Node Q3.DurationTypeSpec [] _) = return DurationType
semanticGraphExpressionTypeFrom (Ast.Node Q3.StretchTypeSpec [] _) = return StretchType
semanticGraphExpressionTypeFrom (Ast.Node Q3.ComplexTypeSpec [maybeSclr] _) =
  ComplexType <$> semanticGraphExpressionTypeFrom maybeSclr
semanticGraphExpressionTypeFrom (Ast.Node Q3.QubitTypeSpec [maybeSize] _) =
  QubitType <$> semanticGraphExpressionFrom maybeSize
semanticGraphExpressionTypeFrom (Ast.Node Q3.ArrayTypeSpec (sclrType : exprs) _) = do
  baseType <- semanticGraphExpressionTypeFrom sclrType
  recurseArrayDimensions baseType exprs
  where
    recurseArrayDimensions :: ExpressionType -> [Q3.SyntaxNode] -> Result ExpressionType
    recurseArrayDimensions innerType [] = return innerType
    recurseArrayDimensions innerType (dimExpr : dimExprs) = do
      newDimExpr <- semanticGraphExpressionFrom dimExpr
      recurseArrayDimensions (ArrayType innerType newDimExpr) dimExprs
semanticGraphExpressionTypeFrom (Ast.Node Q3.ReadonlyArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- semanticGraphExpressionTypeFrom sclrType
  dimCount <- semanticGraphExpressionFrom dimExpr
  return $ ArrayRefType False baseType dimCount
semanticGraphExpressionTypeFrom (Ast.Node Q3.MutableArrayRefTypeSpec [sclrType, dimExpr] _) = do
  baseType <- semanticGraphExpressionTypeFrom sclrType
  dimCount <- semanticGraphExpressionFrom dimExpr
  return $ ArrayRefType True baseType dimCount


{-
semanticGraphFrom (Ast.Node (Q3.DefcalTarget tgt _) [] _) = undefined
semanticGraphFrom (Ast.Node Q3.ArgumentDefinition [anyType, ident] _) = undefined
{- Error cases -}
-- Should have been handled above -- usually implies some change to how the surrounding renders
semanticGraphFrom Ast.NilNode = trace "Unhandled NilNode for semanticGraphFrom" undefined
-- Should have been handled above -- we can't know which separator to use
semanticGraphFrom (Ast.Node Q3.List elems _) = trace ("Unhandled List node for semanticGraphFrom with children: " ++ show elems) undefined
-- Fallback
semanticGraphFrom node = trace ("Missing pattern for semanticGraphFrom: " ++ show node) undefined
-}
