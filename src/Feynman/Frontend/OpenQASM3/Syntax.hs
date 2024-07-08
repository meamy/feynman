{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Feynman.Frontend.OpenQASM3.Syntax
  ( ParseNode,
    Token (..),
    Tag (..),
    pretty,
    normalizeParens,
    tokenIdentifierName,
    tokenIntegerVal,
    tokenFloatVal,
    tokenBooleanVal,
    tokenBitstringVal,
    tokenTimingVal,
    tokenHwQubitIndex,
    tokenVersionMajMin,
    tokenStringVal,
    tokenStr,
  )
where

import Data.Char
import Data.List (intercalate, stripPrefix)
import Data.Maybe (fromMaybe, listToMaybe)
import Debug.Trace (trace)
import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import Numeric
import Text.Read (readMaybe)

type ParseNode = Ast.Node Tag Ast.SourceRef

data Token
  = EofToken
  | OpenqasmToken
  | IncludeToken
  | DefcalgrammarToken
  | DefToken
  | CalToken
  | DefcalToken
  | GateToken
  | ExternToken
  | BoxToken
  | LetToken
  | BreakToken
  | ContinueToken
  | IfToken
  | ElseToken
  | EndToken
  | ReturnToken
  | ForToken
  | WhileToken
  | InToken
  | PragmaToken
  | AnnotationKeywordToken String
  | InputToken
  | OutputToken
  | ConstToken
  | ReadonlyToken
  | MutableToken
  | QregToken
  | QubitToken
  | CregToken
  | BoolToken
  | BitToken
  | IntToken
  | UintToken
  | FloatToken
  | AngleToken
  | ComplexToken
  | ArrayToken
  | VoidToken
  | DurationToken
  | StretchToken
  | GphaseToken
  | InvToken
  | PowToken
  | CtrlToken
  | NegctrlToken
  | DimToken
  | DurationofToken
  | DelayToken
  | ResetToken
  | MeasureToken
  | BarrierToken
  | BooleanLiteralToken String
  | LbracketToken
  | RbracketToken
  | LbraceToken
  | RbraceToken
  | LparenToken
  | RparenToken
  | ColonToken
  | SemicolonToken
  | DotToken
  | CommaToken
  | EqualsToken
  | ArrowToken
  | PlusToken
  | DoublePlusToken
  | MinusToken
  | AsteriskToken
  | DoubleAsteriskToken
  | SlashToken
  | PercentToken
  | PipeToken
  | DoublePipeToken
  | AmpersandToken
  | DoubleAmpersandToken
  | CaretToken
  | AtToken
  | TildeToken
  | ExclamationPointToken
  | -- EqualityOperator
    DoubleEqualsToken
  | ExclamationPointEqualsToken
  | -- CompoundAssignmentOperator
    PlusEqualsToken
  | MinusEqualsToken
  | AsteriskEqualsToken
  | SlashEqualsToken
  | AmpersandEqualsToken
  | PipeEqualsToken
  | TildeEqualsToken
  | CaretEqualsToken
  | DoubleLessEqualsToken
  | DoubleGreaterEqualsToken
  | PercentEqualsToken
  | DoubleAsteriskEqualsToken
  | -- ComparisonOperator
    LessToken
  | GreaterToken
  | LessEqualsToken
  | GreaterEqualsToken
  | -- BitshiftOperator
    DoubleLessToken
  | DoubleGreaterToken
  | --
    ImaginaryLiteralToken String
  | BinaryIntegerLiteralToken String
  | OctalIntegerLiteralToken String
  | DecimalIntegerLiteralToken String
  | HexIntegerLiteralToken String
  | IdentifierToken String
  | HardwareQubitToken String
  | FloatLiteralToken String
  | TimingLiteralToken String
  | BitstringLiteralToken String
  | WhitespaceToken String
  | NewlineToken
  | LineCommentToken String
  | BlockCommentToken String
  | VersionSpecifierToken String
  | StringLiteralToken String
  | RemainingLineContentToken String
  | CalibrationBlockToken String
  deriving (Eq, Ord, Read, Show)

data Timing
  = TimeDt Double
  | TimeNs Double
  | TimeUs Double
  | TimeMs Double
  | TimeS Double
  deriving (Eq, Read, Show)

data Tag
  = Program {openqasmMajorVersion :: Int, openqasmMinorVersion :: Maybe Int, versionTok :: Token} -- [Statement..]
  | Pragma {pragmaContent :: String, pragmaTok :: Token} -- []
  | Statement -- [<StatementContent>, Annotation..]
  | Annotation {annotationName :: String, annotationContent :: String, annotationTok :: Token} -- []
  | Scope -- [Statement..]
  -- <StatementContent>
  | AliasDeclStmt -- [Identifier, Expression..]
  | AssignmentStmt {assignmentOpTok :: Token} -- [IndexedIdentifier, (Expression | MeasureExpr)]
  | BarrierStmt -- [(HardwareQubit | IndexedIdentifier)..]
  | BoxStmt -- [time::Expression?, Scope]
  | BreakStmt -- []
  | CalStmt {calBlockTok :: Token} -- []
  | DefcalgrammarStmt {calgrammarName :: String, calgrammarTok :: Token} -- []
  | ClassicalDeclStmt -- [ScalarTypeSpec | ArrayTypeSpec, Identifier, DeclarationExpr?]
  | ConstDeclStmt -- [ScalarTypeSpec, Identifier, DeclarationExpr]
  | ContinueStmt -- []
  | DefStmt -- [Identifier, List<ArgumentDefinition>, ScalarTypeSpec?, Scope]
  | DefcalStmt -- [DefcalTarget, List<(Expression | ArgumentDefinition)>?, List<HardwareQubit | Identifier>, ScalarTypeSpec?, CalBlock]
  | DelayStmt -- [Expression, (HardwareQubit | IndexedIdentifier)..]
  | EndStmt -- []
  | ExpressionStmt -- [expr]
  | ExternStmt -- [Identifier, List<ScalarTypeSpec>, returnTypeSpec::ScalarTypeSpec?]
  | ForStmt -- [ScalarTypeSpec, Identifier, (Expression | Range | Set), (Statement | Scope)]
  | GateStmt -- [Identifier, List<Identifier>?, List<Identifier>, Scope]
  | GateCallStmt -- [modifiers::List<GateModifier>, target::Identifier, params::List<Expression>?, designator::Expression?, args::List<(HardwareQubit | IndexedIdentifier)>?]
  | IfStmt -- [condition::Expression, thenBlock::(Statement | Scope), elseBlock::(Statement | Scope)?
  | IncludeStmt {includePath :: String, includeTok :: Token} -- []
  | InputIoDeclStmt -- [(ScalarTypeSpec | ArrayTypeSpec), Identifier]
  | OutputIoDeclStmt -- [(ScalarTypeSpec | ArrayTypeSpec), Identifier]
  | MeasureArrowAssignmentStmt -- [(HardwareQubit | IndexedIdentifier), IndexedIdentifier?]
  | CregOldStyleDeclStmt -- [Identifier, designator::Expression?]
  | QregOldStyleDeclStmt -- [Identifier, designator::Expression?]
  | QuantumDeclStmt -- [QubitTypeSpec, Identifier]
  | ResetStmt -- [(HardwareQubit | IndexedIdentifier)]
  | ReturnStmt -- [(Expression | MeasureExpr)?]
  | WhileStmt -- [Expression, (Statement | Scope)]
  -- <Expression>
  | ParenExpr -- [Expression]
  | IndexExpr -- [Expression, (List<RangeInitExpr | Expression> | SetInitExpr)]
  | UnaryOperatorExpr {unaryOp :: Token} -- [Expression]
  | BinaryOperatorExpr {binaryOp :: Token} -- [left::Expression, right::Expression]
  | CastExpr -- [(ScalarTypeSpec | ArrayTypeSpec), Expression]
  | DurationOfExpr -- [Scope]
  | CallExpr -- [Identifier, List<ExpressionNode>]
  --   Array only allowed in array initializers
  | ArrayInitExpr -- [elements::Expression..]
  --   Set, Range only allowed in (some) indexing expressions
  | SetInitExpr -- [elements::Expression..]
  | RangeInitExpr -- [begin::Expression?, step::Expression?, end::Expression?]
  --   Dim only allowed in (some) array arg definitions
  | DimExpr -- [size]
  | MeasureExpr -- [expr]
  | Identifier {identifierName :: String, identifierTok :: Token} -- []
  | IntegerLiteral {integerVal :: Integer, integerTok :: Token} -- []
  | FloatLiteral {floatVal :: Double, floatTok :: Token} -- []
  | ImaginaryLiteral {imaginaryVal :: Double, imaginaryTok :: Token} -- []
  | BooleanLiteral {booleanVal :: Bool, booleanTok :: Token} -- []
  | BitstringLiteral {bitstringVal :: [Bool], bitstringTok :: Token} -- []
  | TimingLiteral {timingVal :: Timing, timingTok :: Token} -- []
  | HardwareQubit {hwQubitIndex :: Int, hwQubitTok :: Token} -- []
  --
  | IndexedIdentifier -- [Identifier, (List<RangeInitExpr | Expression> | SetInitExpr)]
  -- <GateModifier>
  | InvGateModifier -- []
  | PowGateModifier -- [Expression]
  | CtrlGateModifier -- [Expression?]
  | NegCtrlGateModifier -- [Expression?]
  -- <ScalarTypeSpec>
  | BitTypeSpec -- [size::Expression?]
  | IntTypeSpec -- [size::Expression?]
  | UintTypeSpec -- [size::Expression?]
  | FloatTypeSpec -- [size::Expression?]
  | AngleTypeSpec -- [size::Expression?]
  | BoolTypeSpec
  | DurationTypeSpec
  | StretchTypeSpec
  | ComplexTypeSpec -- [base::ScalarTypeSpec?]
  | CregTypeSpec -- [size::Expression?]
  | QregTypeSpec -- [size::Expression?]
  -- Special types
  | QubitTypeSpec -- [size::Expression?]
  | ArrayTypeSpec -- [base::ScalarTypeSpec, indices::Expression..]
  -- <ArrayReferenceTypeSpec>
  | ReadonlyArrayRefTypeSpec -- [base::ScalarTypeSpec, sizes::(DimExpr | List<Expression>)]
  | MutableArrayRefTypeSpec -- [base::ScalarTypeSpec, sizes::(DimExpr | List<Expression>)]
  --
  | DefcalTarget {defcalTargetName :: String, defcalTargetTok :: Token} -- []
  | ArgumentDefinition -- [{Scalar,Qubit,Creg,Qreg,*ArrayRef}TypeSpec, Identifier]
  | List -- [element..]
  deriving (Eq, Read, Show)

-- Convert the syntax tree back into a string form that can be parsed into an
-- equivalent tree
pretty :: Ast.Node Tag c -> String
pretty (Ast.Node (Program _ _ EofToken) stmts _) =
  concatMap ((++ "\n") . pretty) stmts
pretty (Ast.Node (Program _ _ tok) stmts _) =
  "OPENQASM " ++ tokenStr tok ++ ";\n\n" ++ concatMap ((++ "\n") . pretty) stmts
pretty (Ast.Node (Pragma ctnt _) [] _) = "pragma " ++ ctnt
pretty (Ast.Node Statement (stmt : annots) _) = concatMap ((++ "\n") . pretty) annots ++ pretty stmt
pretty (Ast.Node (Annotation name ctnt _) [] _) = '@' : name ++ " " ++ ctnt
pretty (Ast.Node Scope [] _) = "{ }"
pretty (Ast.Node Scope [stmt] _) = "{ " ++ pretty stmt ++ " }"
pretty (Ast.Node Scope stmts _) = "{\n" ++ indent (concatMap ((++ "\n") . pretty) stmts) ++ "}"
pretty (Ast.Node AliasDeclStmt (ident : exprs) _) =
  "let " ++ pretty ident ++ " = " ++ intercalate " ++ " (map pretty exprs) ++ ";"
pretty (Ast.Node (AssignmentStmt op) [target, expr] _) = pretty target ++ " " ++ tokenStr op ++ " " ++ pretty expr ++ ";"
pretty (Ast.Node BarrierStmt gateOperands _) = "barrier " ++ prettyListElements gateOperands ++ ";"
pretty (Ast.Node BoxStmt [time, scope] _) = "box" ++ prettyMaybeDsgn time ++ " " ++ pretty scope
pretty (Ast.Node BreakStmt [] _) = "break;"
pretty (Ast.Node (CalStmt calBlock) [] _) = tokenStr calBlock
pretty (Ast.Node (DefcalgrammarStmt _ cgname) [] _) = "defcalgrammar " ++ tokenStr cgname ++ ";"
pretty (Ast.Node ClassicalDeclStmt [anyType, ident, maybeExpr] _) =
  pretty anyType ++ " " ++ pretty ident ++ prettyMaybe " = " maybeExpr "" ++ ";"
pretty (Ast.Node ConstDeclStmt [sclrType, ident, maybeExpr] _) =
  "const " ++ pretty sclrType ++ " " ++ pretty ident ++ prettyMaybe " = " maybeExpr "" ++ ";"
pretty (Ast.Node ContinueStmt [] _) = "continue;"
pretty (Ast.Node DefStmt [ident, argDefs, returnType, scope] _) =
  "def "
    ++ pretty ident
    ++ "("
    ++ prettyList argDefs
    ++ ")"
    ++ prettyReturnType returnType
    ++ " "
    ++ pretty scope
pretty (Ast.Node DelayStmt (designator : gateOperands) _) = "delay[" ++ pretty designator ++ "] " ++ prettyListElements gateOperands ++ ";"
pretty (Ast.Node DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  "defcal "
    ++ pretty defcalTarget
    ++ (if Ast.isNilNode defcalArgs then " " else "(" ++ prettyList defcalArgs ++ ") ")
    ++ prettyList defcalOps
    ++ prettyReturnType returnType
    ++ " "
    ++ pretty calBlock
pretty (Ast.Node EndStmt [] _) = "end;"
pretty (Ast.Node ExpressionStmt [expr] _) = pretty expr ++ ";"
pretty (Ast.Node ExternStmt [ident, paramTypes, returnType] _) =
  -- paramTypes are scalar, arrayRef, or CREG
  "extern " ++ pretty ident ++ "(" ++ prettyList paramTypes ++ ")" ++ prettyReturnType returnType ++ ";"
pretty (Ast.Node ForStmt [anyType, ident, loopExpr@(Ast.Node RangeInitExpr _ _), loopStmt] _) =
  "for " ++ pretty anyType ++ " " ++ pretty ident ++ " in [" ++ pretty loopExpr ++ "] " ++ pretty loopStmt
pretty (Ast.Node ForStmt [anyType, ident, loopExpr, loopStmt] _) =
  "for " ++ pretty anyType ++ " " ++ pretty ident ++ " in " ++ pretty loopExpr ++ " " ++ pretty loopStmt
pretty (Ast.Node GateStmt [ident, params, args, stmts] _) =
  "gate "
    ++ pretty ident
    ++ (if Ast.isNilNode params then "" else "(" ++ prettyList params ++ ")")
    ++ (if Ast.isNilNode args then "" else ' ' : prettyList args)
    ++ " "
    ++ pretty stmts
pretty (Ast.Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) =
  ( case modifiers of
      Ast.NilNode -> ""
      Ast.Node {Ast.children = cs} -> concatMap ((++ " ") . pretty) cs
  )
    ++ pretty target
    ++ prettyMaybeList "(" params ")"
    ++ prettyMaybe "[" maybeTime "]"
    ++ prettyMaybeList " " gateArgs ""
    ++ ";"
pretty (Ast.Node IfStmt [condExpr, thenBlock, maybeElseBlock] _) =
  "if (" ++ pretty condExpr ++ ") " ++ pretty thenBlock ++ prettyMaybe " else " maybeElseBlock ""
pretty (Ast.Node (IncludeStmt _ tok) [] _) = "include " ++ tokenStr tok ++ ";"
pretty (Ast.Node InputIoDeclStmt [anyType, ident] _) = "input " ++ pretty anyType ++ " " ++ pretty ident ++ ";"
pretty (Ast.Node OutputIoDeclStmt [anyType, ident] _) = "output " ++ pretty anyType ++ " " ++ pretty ident ++ ";"
pretty (Ast.Node MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) =
  pretty msrExpr ++ prettyMaybe " -> " maybeTgt "" ++ ";"
pretty (Ast.Node CregOldStyleDeclStmt [ident, maybeSize] _) = "creg " ++ pretty ident ++ prettyMaybeDsgn maybeSize ++ ";"
pretty (Ast.Node QregOldStyleDeclStmt [ident, maybeSize] _) = "qreg " ++ pretty ident ++ prettyMaybeDsgn maybeSize ++ ";"
pretty (Ast.Node QuantumDeclStmt [qubitType, ident] _) = pretty qubitType ++ " " ++ pretty ident ++ ";"
pretty (Ast.Node ResetStmt [gateOp] _) = "reset " ++ pretty gateOp ++ ";"
pretty (Ast.Node ReturnStmt [maybeExpr] _) = "return" ++ prettyMaybe " " maybeExpr "" ++ ";"
pretty (Ast.Node WhileStmt [condExpr, loopBlock] _) = "while (" ++ pretty condExpr ++ ") " ++ pretty loopBlock
pretty (Ast.Node ParenExpr [expr] _) = "(" ++ pretty expr ++ ")"
pretty (Ast.Node IndexExpr [expr, index] _) = pretty expr ++ "[" ++ prettyIndex index ++ "]"
pretty (Ast.Node (UnaryOperatorExpr op) [expr] _) = tokenStr op ++ pretty expr
pretty (Ast.Node (BinaryOperatorExpr op) [left, right] _) =
  pretty left ++ " " ++ tokenStr op ++ " " ++ pretty right
pretty (Ast.Node CastExpr [anyType, expr] _) = pretty anyType ++ "(" ++ pretty expr ++ ")"
pretty (Ast.Node DurationOfExpr [scope] _) = "durationof( " ++ pretty scope ++ " )"
pretty (Ast.Node CallExpr [ident, params] _) = pretty ident ++ "(" ++ prettyList params ++ ")"
pretty (Ast.Node (Identifier _ tok) [] _) = tokenStr tok
pretty (Ast.Node (IntegerLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (FloatLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (ImaginaryLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (BooleanLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (BitstringLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (TimingLiteral _ tok) [] _) = tokenStr tok
pretty (Ast.Node (HardwareQubit _ tok) [] _) = tokenStr tok
pretty (Ast.Node ArrayInitExpr elems _) = "{" ++ prettyListElements elems ++ "}"
pretty (Ast.Node SetInitExpr elems _) = "{" ++ prettyListElements elems ++ "}"
pretty (Ast.Node RangeInitExpr [begin, step, end] _) =
  prettyMaybe "" begin "" ++ ":" ++ prettyMaybe "" step ":" ++ prettyMaybe "" end ""
pretty (Ast.Node DimExpr [size] _) = "#dim=" ++ pretty size
pretty (Ast.Node MeasureExpr [gateOp] _) = "measure " ++ pretty gateOp
pretty (Ast.Node IndexedIdentifier [ident, index] _) = pretty ident ++ "[" ++ prettyIndex index ++ "]"
pretty (Ast.Node InvGateModifier [] _) = "inv @"
pretty (Ast.Node PowGateModifier [expr] _) = "pow(" ++ pretty expr ++ ") @"
pretty (Ast.Node CtrlGateModifier [maybeExpr] _) = "ctrl " ++ prettyMaybe "(" maybeExpr ") " ++ "@"
pretty (Ast.Node NegCtrlGateModifier [maybeExpr] _) = "negctrl " ++ prettyMaybe "(" maybeExpr ") " ++ "@"
pretty (Ast.Node BitTypeSpec [maybeSize] _) = "bit" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node CregTypeSpec [maybeSize] _) = "creg" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node QregTypeSpec [maybeSize] _) = "qreg" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node IntTypeSpec [maybeSize] _) = "int" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node UintTypeSpec [maybeSize] _) = "uint" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node FloatTypeSpec [maybeSize] _) = "float" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node AngleTypeSpec [maybeSize] _) = "angle" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node BoolTypeSpec [] _) = "bool"
pretty (Ast.Node DurationTypeSpec [] _) = "duration"
pretty (Ast.Node StretchTypeSpec [] _) = "stretch"
pretty (Ast.Node ComplexTypeSpec [maybeSclr] _) = "complex" ++ prettyMaybeDsgn maybeSclr
pretty (Ast.Node QubitTypeSpec [maybeSize] _) = "qubit" ++ prettyMaybeDsgn maybeSize
pretty (Ast.Node ArrayTypeSpec (sclrType : exprs) _) =
  "array[" ++ pretty sclrType ++ ", " ++ prettyListElements exprs ++ "]"
pretty (Ast.Node ReadonlyArrayRefTypeSpec [sclrType, exprs@(Ast.Node List _ _)] _) =
  "readonly array[" ++ pretty sclrType ++ ", " ++ prettyList exprs ++ "]"
pretty (Ast.Node MutableArrayRefTypeSpec [sclrType, exprs@(Ast.Node List _ _)] _) =
  "mutable array[" ++ pretty sclrType ++ ", " ++ prettyList exprs ++ "]"
pretty (Ast.Node ReadonlyArrayRefTypeSpec [sclrType, dimExpr@(Ast.Node DimExpr _ _)] _) =
  "readonly array[" ++ pretty sclrType ++ ", " ++ pretty dimExpr ++ "]"
pretty (Ast.Node MutableArrayRefTypeSpec [sclrType, dimExpr@(Ast.Node DimExpr _ _)] _) =
  "mutable array[" ++ pretty sclrType ++ ", " ++ pretty dimExpr ++ "]"
pretty (Ast.Node (DefcalTarget tgt _) [] _) = tgt -- "measure", "reset", "delay", or some other identifier
-- does not handle CREG, QREG args (postfix size designator)
pretty (Ast.Node ArgumentDefinition [anyType, ident] _) = pretty anyType ++ " " ++ pretty ident
{- Error cases -}
-- Should have been handled above -- usually implies some change to how the surrounding renders
pretty Ast.NilNode = trace "Unhandled NilNode for pretty" undefined
-- Should have been handled above -- we can't know which separator to use
pretty (Ast.Node List elems _) = trace ("Unhandled List node for pretty with children: " ++ show (map pretty elems)) undefined
-- Fallback
pretty (Ast.Node tag elems _) = trace ("Missing pattern for pretty: Ast.Node " ++ show tag ++ " " ++ show (map pretty elems)) undefined

-- The syntax tree is as close to canonicalized as the tree easily gets
normalizeParens :: Ast.Node Tag c ->  Ast.Node Tag c
normalizeParens Ast.NilNode = Ast.NilNode
-- Strip extra parens
normalizeParens (Ast.Node ParenExpr [expr] _) = normalizeParens expr
normalizeParens (Ast.Node ParenExpr children _) = undefined
-- Parenthesize nontrivial expressions associated with index operators
normalizeParens (Ast.Node IndexExpr [expr, list] ctx) =
  Ast.Node IndexExpr [parenthesizeNonTrivialExpr $ normalizeParens expr, normalizeParens list] ctx
normalizeParens (Ast.Node IndexExpr children _) = undefined
-- Parenthesize nontrivial expressions associated with other unary operators
normalizeParens (Ast.Node unop@(UnaryOperatorExpr _) [expr] ctx) =
  Ast.Node unop [parenthesizeNonTrivialExpr $ normalizeParens expr] ctx
normalizeParens (Ast.Node (UnaryOperatorExpr _) children _) = undefined
-- Parenthesize nontrivial expressions associated with binary operators
normalizeParens (Ast.Node binop@(BinaryOperatorExpr _) [exprA, exprB] ctx) =
  Ast.Node binop [parenthesizeNonTrivialExpr $ normalizeParens exprA, parenthesizeNonTrivialExpr $ normalizeParens exprB] ctx
normalizeParens (Ast.Node (BinaryOperatorExpr _) children _) = undefined
-- Pass everything else through untouched
normalizeParens (Ast.Node tag children ctx) = Ast.Node tag (map normalizeParens children) ctx

parenthesizeNonTrivialExpr :: Ast.Node Tag c -> Ast.Node Tag c
parenthesizeNonTrivialExpr expr =
  if isTrivialExpr expr then expr else Ast.Node ParenExpr [expr] (Ast.context expr)
  where
    isTrivialExpr (Ast.Node ParenExpr _ _) = True
    isTrivialExpr (Ast.Node CastExpr _ _) = True
    isTrivialExpr (Ast.Node DurationOfExpr _ _) = True
    isTrivialExpr (Ast.Node CallExpr _ _) = True
    isTrivialExpr (Ast.Node (Identifier _ _) [] _) = True
    isTrivialExpr (Ast.Node (IntegerLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (FloatLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (ImaginaryLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (BooleanLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (BitstringLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (TimingLiteral _ _) [] _) = True
    isTrivialExpr (Ast.Node (HardwareQubit _ _) [] _) = True
    isTrivialExpr (Ast.Node ArrayInitExpr _ _) = True
    isTrivialExpr (Ast.Node SetInitExpr _ _) = True
    isTrivialExpr _ = False

-- Utility functions

tokenIdentifierName :: Token -> String
tokenIdentifierName (IdentifierToken str) = str
tokenIdentifierName (AnnotationKeywordToken ('@' : str)) = str
tokenIdentifierName (AnnotationKeywordToken str) = str

tokenIntegerVal :: Token -> Integer
tokenIntegerVal tok =
  case tok of
    BinaryIntegerLiteralToken str -> readLiteral readBin $ stripPrefix 'b' str
    OctalIntegerLiteralToken str -> readLiteral readOct $ stripPrefix 'o' str
    DecimalIntegerLiteralToken str -> readLiteral readDec str
    HexIntegerLiteralToken str -> readLiteral readHex $ stripPrefix 'x' str
  where
    stripPrefix lc (x : y : remain) | x == '0' && toLower y == lc = remain
    readLiteral f str = case f str of [(val, "")] -> val

tokenFloatVal :: Token -> Double
tokenFloatVal (FloatLiteralToken str) = case readFloat str of [(val, "")] -> val
tokenFloatVal (ImaginaryLiteralToken str) = case readFloat str of [(val, "im")] -> val

tokenBooleanVal :: Token -> Bool
tokenBooleanVal (BooleanLiteralToken str) = str == "true"

tokenBitstringVal :: Token -> [Bool]
tokenBitstringVal (BitstringLiteralToken str) = (readLiteral . stripQuotes) str
  where
    stripQuotes = removeFirstQ . reverse . removeFirstQ . reverse
    removeFirstQ ('"' : remain) = remain
    readLiteral "" = []
    readLiteral ('0' : remain) = False : readLiteral remain
    readLiteral ('1' : remain) = True : readLiteral remain

tokenTimingVal :: Token -> Timing
tokenTimingVal (TimingLiteralToken str) = undefined

tokenHwQubitIndex :: Token -> Int
tokenHwQubitIndex (HardwareQubitToken ('$' : remain)) = case readDec remain of [(index, "")] -> index

tokenVersionMajMin :: Token -> (Int, Maybe Int)
tokenVersionMajMin (VersionSpecifierToken str) =
  let split sep [] = ([], Nothing)
      split sep (x : xs) =
        if x == sep
          then ([], Just xs)
          else let (foundHead, foundTail) = split sep xs in (x : foundHead, foundTail)
      (major, minor) = split '.' str
      majorVal = fromMaybe (-1) (readMaybe major)
      minorVal = case minor of Nothing -> Nothing; Just "" -> Nothing; Just minorStr -> readMaybe minorStr
   in (majorVal, minorVal)

tokenStringVal :: Token -> String
tokenStringVal (StringLiteralToken ('"' : strTail)) =
  case reverse strTail of
    '"' : strMid -> reverse strMid
    _ -> strTail
tokenStringVal (StringLiteralToken str) = str
tokenStringVal (RemainingLineContentToken str) = str
tokenStringVal (CalibrationBlockToken str) = str

tokenStr :: Token -> String
tokenStr EofToken = ""
tokenStr OpenqasmToken = "OPENQASM"
tokenStr IncludeToken = "include"
tokenStr DefcalgrammarToken = "defcalgrammar"
tokenStr DefToken = "def"
tokenStr CalToken = "cal"
tokenStr DefcalToken = "defcal"
tokenStr GateToken = "gate"
tokenStr ExternToken = "extern"
tokenStr BoxToken = "box"
tokenStr LetToken = "let"
tokenStr BreakToken = "break"
tokenStr ContinueToken = "continue"
tokenStr IfToken = "if"
tokenStr ElseToken = "else"
tokenStr EndToken = "end"
tokenStr ReturnToken = "return"
tokenStr ForToken = "for"
tokenStr WhileToken = "while"
tokenStr InToken = "in"
tokenStr PragmaToken = "#pragma"
tokenStr (AnnotationKeywordToken kw) = kw
tokenStr InputToken = "input"
tokenStr OutputToken = "output"
tokenStr ConstToken = "const"
tokenStr ReadonlyToken = "readonly"
tokenStr MutableToken = "mutable"
tokenStr QregToken = "qreg"
tokenStr QubitToken = "qubit"
tokenStr CregToken = "creg"
tokenStr BoolToken = "bool"
tokenStr BitToken = "bit"
tokenStr IntToken = "int"
tokenStr UintToken = "uint"
tokenStr FloatToken = "float"
tokenStr AngleToken = "angle"
tokenStr ComplexToken = "complex"
tokenStr ArrayToken = "array"
tokenStr VoidToken = "void"
tokenStr DurationToken = "duration"
tokenStr StretchToken = "stretch"
tokenStr GphaseToken = "gphase"
tokenStr InvToken = "inv"
tokenStr PowToken = "pow"
tokenStr CtrlToken = "ctrl"
tokenStr NegctrlToken = "negctrl"
tokenStr DimToken = "dim"
tokenStr DurationofToken = "durationof"
tokenStr DelayToken = "delay"
tokenStr ResetToken = "reset"
tokenStr MeasureToken = "measure"
tokenStr BarrierToken = "barrier"
tokenStr (BooleanLiteralToken str) = str
tokenStr LbracketToken = "["
tokenStr RbracketToken = "]"
tokenStr LbraceToken = "{"
tokenStr RbraceToken = "}"
tokenStr LparenToken = "("
tokenStr RparenToken = ")"
tokenStr ColonToken = ":"
tokenStr SemicolonToken = ";"
tokenStr DotToken = "."
tokenStr CommaToken = ","
tokenStr EqualsToken = "="
tokenStr ArrowToken = "->"
tokenStr PlusToken = "+"
tokenStr DoublePlusToken = "++"
tokenStr MinusToken = "-"
tokenStr AsteriskToken = "*"
tokenStr DoubleAsteriskToken = "**"
tokenStr SlashToken = "/"
tokenStr PercentToken = "%"
tokenStr PipeToken = "|"
tokenStr DoublePipeToken = "||"
tokenStr AmpersandToken = "&"
tokenStr DoubleAmpersandToken = "&&"
tokenStr CaretToken = "^"
tokenStr AtToken = "@"
tokenStr TildeToken = "~"
tokenStr ExclamationPointToken = "!"
tokenStr DoubleEqualsToken = "=="
tokenStr ExclamationPointEqualsToken = "!="
tokenStr PlusEqualsToken = "+="
tokenStr MinusEqualsToken = "-="
tokenStr AsteriskEqualsToken = "*="
tokenStr SlashEqualsToken = "/="
tokenStr AmpersandEqualsToken = "&="
tokenStr PipeEqualsToken = "|="
tokenStr TildeEqualsToken = "~="
tokenStr CaretEqualsToken = "^="
tokenStr DoubleLessEqualsToken = "<<="
tokenStr DoubleGreaterEqualsToken = ">>="
tokenStr PercentEqualsToken = "%="
tokenStr DoubleAsteriskEqualsToken = "**="
tokenStr LessToken = "<"
tokenStr GreaterToken = ">"
tokenStr LessEqualsToken = "<="
tokenStr GreaterEqualsToken = ">="
tokenStr DoubleLessToken = "<<"
tokenStr DoubleGreaterToken = ">>"
tokenStr (ImaginaryLiteralToken str) = str
tokenStr (BinaryIntegerLiteralToken str) = str
tokenStr (OctalIntegerLiteralToken str) = str
tokenStr (DecimalIntegerLiteralToken str) = str
tokenStr (HexIntegerLiteralToken str) = str
tokenStr (IdentifierToken str) = str
tokenStr (HardwareQubitToken str) = str
tokenStr (FloatLiteralToken str) = str
tokenStr (TimingLiteralToken str) = str
tokenStr (BitstringLiteralToken str) = str
tokenStr (WhitespaceToken str) = str
tokenStr NewlineToken = "\n"
tokenStr (LineCommentToken str) = str
tokenStr (BlockCommentToken str) = str
tokenStr (VersionSpecifierToken str) = str
tokenStr (StringLiteralToken str) = str
tokenStr (RemainingLineContentToken str) = str
tokenStr (CalibrationBlockToken str) = str

prettyTiming :: Timing -> String
prettyTiming (TimeDt t) = show t ++ "dt"
prettyTiming (TimeNs t) = show t ++ "ns"
prettyTiming (TimeUs t) = show t ++ "us"
prettyTiming (TimeMs t) = show t ++ "ms"
prettyTiming (TimeS t) = show t ++ "s"

prettyIndex :: Ast.Node Tag c -> String
prettyIndex idx = if Ast.tag idx == List then prettyList idx else pretty idx

prettyList :: Ast.Node Tag c -> String
prettyList Ast.NilNode = ""
prettyList (Ast.Node List elems _) = prettyListElements elems

prettyMaybeDsgn :: Ast.Node Tag c -> String
prettyMaybeDsgn expr = prettyMaybe "[" expr "]"

prettyMaybeList :: String -> Ast.Node Tag c -> String -> String
prettyMaybeList _ Ast.NilNode _ = ""
prettyMaybeList pre (Ast.Node List elems _) post = pre ++ prettyListElements elems ++ post

prettyMaybe :: String -> Ast.Node Tag c -> String -> String
prettyMaybe _ Ast.NilNode _ = ""
prettyMaybe pre expr post = pre ++ pretty expr ++ post

prettyListElements :: [Ast.Node Tag c] -> String
prettyListElements elems = intercalate ", " (map pretty elems)

prettyReturnType :: Ast.Node Tag c -> String
prettyReturnType Ast.NilNode = ""
prettyReturnType returnType = " -> " ++ pretty returnType

indent :: String -> String
indent block = concatMap (\s -> "  " ++ s ++ "\n") $ lines block
