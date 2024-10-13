{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Feynman.Frontend.OpenQASM3.Syntax
  ( ParseNode,
    Token (..),
    Tag (..),
    isEmptyStatement,
    pruneEmptyStatements,
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
    withContext,
    node,
    programNode,
    stmtNode,
    withAnnotations,
    binOpNode,
    unOpNode,
    identifierNode,
    integerLiteralNode,
    floatLiteralNode,
    imaginaryLiteralNode,
    booleanLiteralNode,
    bitstringLiteralNode,
  )
where

import Control.DeepSeq (NFData)
import Data.Char
import Data.List (intercalate, stripPrefix)
import Data.Maybe (fromMaybe, listToMaybe)
import Debug.Trace (trace)
import Feynman.Frontend.OpenQASM3.Ast
import GHC.Generics (Generic)
import Numeric (readDec, readFloat, readHex, readOct)
import Text.Read (readMaybe)

type ParseNode = Node Tag SourceRef

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
  deriving (Eq, Ord, Read, Show, Generic)

data Timing
  = TimeDt Double
  | TimeNs Double
  | TimeUs Double
  | TimeMs Double
  | TimeS Double
  deriving (Eq, Read, Show, Generic)

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
  | ClassicalDeclStmt -- [ScalarTypeSpec | ArrayTypeSpec, Identifier, InitializerExpr?]
  | ConstDeclStmt -- [ScalarTypeSpec, Identifier, InitializerExpr]
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
  | IfStmt -- [condition::Expression, then::(Statement | Scope), else::(Statement | Scope)?
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
  deriving (Eq, Read, Show, Generic)

instance NFData Token

instance NFData Timing

instance NFData Tag

isEmptyStatement :: Node Tag c -> Bool
isEmptyStatement NilNode = True
isEmptyStatement (Node Statement (NilNode : _) _) = True
isEmptyStatement _ = False

pruneEmptyStatements :: Node Tag c -> Node Tag c
pruneEmptyStatements NilNode = NilNode
pruneEmptyStatements pgm@(Node (Program {}) statements _) =
  pgm {children = filter (not . isEmptyStatement) (map pruneEmptyStatements statements)}
pruneEmptyStatements scope@(Node Scope statements _) =
  scope {children = filter (not . isEmptyStatement) (map pruneEmptyStatements statements)}
pruneEmptyStatements node@(Node _ children _) = node {children = map pruneEmptyStatements children}

-- Convert the syntax tree back into a string form that can be parsed into an
-- equivalent tree
pretty :: Node Tag c -> String
pretty (Node (Program _ _ EofToken) stmts _) =
  let prunedStmts = filter (not . isEmptyStatement) stmts
   in concatMap ((++ "\n") . pretty) prunedStmts
pretty (Node (Program _ _ tok) stmts _) =
  "OPENQASM " ++ tokenStr tok ++ ";\n\n" ++ concatMap ((++ "\n") . pretty) stmts
pretty (Node (Pragma ctnt _) [] _) = "pragma " ++ ctnt
pretty (Node Statement (stmt : annots) _) = concatMap ((++ "\n") . pretty) annots ++ pretty stmt
pretty (Node (Annotation name ctnt _) [] _) = '@' : name ++ " " ++ ctnt
pretty (Node Scope stmts _) =
  let prunedStmts = filter (not . isEmptyStatement) stmts
   in case prunedStmts of
        [] -> "{ }"
        [stmt] -> "{ " ++ pretty stmt ++ " }"
        _ -> "{\n" ++ indent (concatMap ((++ "\n") . pretty) prunedStmts) ++ "}"
pretty (Node AliasDeclStmt (ident : exprs) _) =
  "let " ++ pretty ident ++ " = " ++ intercalate " ++ " (map pretty exprs) ++ ";"
pretty (Node (AssignmentStmt op) [target, expr] _) = pretty target ++ " " ++ tokenStr op ++ " " ++ pretty expr ++ ";"
pretty (Node BarrierStmt gateOperands _) = "barrier " ++ prettyListElements gateOperands ++ ";"
pretty (Node BoxStmt [time, scope] _) = "box" ++ prettyMaybeDsgn time ++ " " ++ pretty scope
pretty (Node BreakStmt [] _) = "break;"
pretty (Node (CalStmt calBlock) [] _) = tokenStr calBlock
pretty (Node (DefcalgrammarStmt _ cgname) [] _) = "defcalgrammar " ++ tokenStr cgname ++ ";"
pretty (Node ClassicalDeclStmt [anyType, ident, maybeExpr] _) =
  pretty anyType ++ " " ++ pretty ident ++ prettyMaybe " = " maybeExpr "" ++ ";"
pretty (Node ConstDeclStmt [sclrType, ident, maybeExpr] _) =
  "const " ++ pretty sclrType ++ " " ++ pretty ident ++ prettyMaybe " = " maybeExpr "" ++ ";"
pretty (Node ContinueStmt [] _) = "continue;"
pretty (Node DefStmt [ident, argDefs, returnType, scope] _) =
  "def "
    ++ pretty ident
    ++ "("
    ++ prettyList argDefs
    ++ ")"
    ++ prettyReturnType returnType
    ++ " "
    ++ pretty scope
pretty (Node DelayStmt (designator : gateOperands) _) = "delay[" ++ pretty designator ++ "] " ++ prettyListElements gateOperands ++ ";"
pretty (Node DefcalStmt [defcalTarget, defcalArgs, defcalOps, returnType, calBlock] _) =
  "defcal "
    ++ pretty defcalTarget
    ++ (if isNilNode defcalArgs then " " else "(" ++ prettyList defcalArgs ++ ") ")
    ++ prettyList defcalOps
    ++ prettyReturnType returnType
    ++ " "
    ++ pretty calBlock
pretty (Node EndStmt [] _) = "end;"
pretty (Node ExpressionStmt [expr] _) = pretty expr ++ ";"
pretty (Node ExternStmt [ident, paramTypes, returnType] _) =
  -- paramTypes are scalar, arrayRef, or CREG
  "extern " ++ pretty ident ++ "(" ++ prettyList paramTypes ++ ")" ++ prettyReturnType returnType ++ ";"
pretty (Node ForStmt [anyType, ident, loopExpr@(Node RangeInitExpr _ _), loopStmt] _) =
  "for " ++ pretty anyType ++ " " ++ pretty ident ++ " in [" ++ pretty loopExpr ++ "] " ++ pretty loopStmt
pretty (Node ForStmt [anyType, ident, loopExpr, loopStmt] _) =
  "for " ++ pretty anyType ++ " " ++ pretty ident ++ " in " ++ pretty loopExpr ++ " " ++ pretty loopStmt
pretty (Node GateStmt [ident, params, args, stmts] _) =
  "gate "
    ++ pretty ident
    ++ (if isNilNode params then "" else "(" ++ prettyList params ++ ")")
    ++ (if isNilNode args then "" else ' ' : prettyList args)
    ++ " "
    ++ pretty stmts
pretty (Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] _) =
  ( case modifiers of
      NilNode -> ""
      Node {children = cs} -> concatMap ((++ " ") . pretty) cs
  )
    ++ pretty target
    ++ prettyMaybeList "(" params ")"
    ++ prettyMaybe "[" maybeTime "]"
    ++ prettyMaybeList " " gateArgs ""
    ++ ";"
pretty (Node IfStmt [condExpr, thenBlock, maybeElseBlock] _) =
  "if (" ++ pretty condExpr ++ ") " ++ pretty thenBlock ++ prettyMaybe " else " maybeElseBlock ""
pretty (Node (IncludeStmt _ tok) [] _) = "include " ++ tokenStr tok ++ ";"
pretty (Node InputIoDeclStmt [anyType, ident] _) = "input " ++ pretty anyType ++ " " ++ pretty ident ++ ";"
pretty (Node OutputIoDeclStmt [anyType, ident] _) = "output " ++ pretty anyType ++ " " ++ pretty ident ++ ";"
pretty (Node MeasureArrowAssignmentStmt [msrExpr, maybeTgt] _) =
  pretty msrExpr ++ prettyMaybe " -> " maybeTgt "" ++ ";"
pretty (Node CregOldStyleDeclStmt [ident, maybeSize] _) = "creg " ++ pretty ident ++ prettyMaybeDsgn maybeSize ++ ";"
pretty (Node QregOldStyleDeclStmt [ident, maybeSize] _) = "qreg " ++ pretty ident ++ prettyMaybeDsgn maybeSize ++ ";"
pretty (Node QuantumDeclStmt [qubitType, ident] _) = pretty qubitType ++ " " ++ pretty ident ++ ";"
pretty (Node ResetStmt [gateOp] _) = "reset " ++ pretty gateOp ++ ";"
pretty (Node ReturnStmt [maybeExpr] _) = "return" ++ prettyMaybe " " maybeExpr "" ++ ";"
pretty (Node WhileStmt [condExpr, loopBlock] _) = "while (" ++ pretty condExpr ++ ") " ++ pretty loopBlock
pretty (Node ParenExpr [expr] _) = "(" ++ pretty expr ++ ")"
pretty (Node IndexExpr [expr, index] _) = pretty expr ++ "[" ++ prettyIndex index ++ "]"
pretty (Node (UnaryOperatorExpr op) [expr] _) = tokenStr op ++ pretty expr
pretty (Node (BinaryOperatorExpr op) [left, right] _) =
  pretty left ++ " " ++ tokenStr op ++ " " ++ pretty right
pretty (Node CastExpr [anyType, expr] _) = pretty anyType ++ "(" ++ pretty expr ++ ")"
pretty (Node DurationOfExpr [scope] _) = "durationof( " ++ pretty scope ++ " )"
pretty (Node CallExpr [ident, params] _) = pretty ident ++ "(" ++ prettyList params ++ ")"
pretty (Node (Identifier _ tok) [] _) = tokenStr tok
pretty (Node (IntegerLiteral _ tok) [] _) = tokenStr tok
pretty (Node (FloatLiteral _ tok) [] _) = tokenStr tok
pretty (Node (ImaginaryLiteral _ tok) [] _) = tokenStr tok
pretty (Node (BooleanLiteral _ tok) [] _) = tokenStr tok
pretty (Node (BitstringLiteral _ tok) [] _) = tokenStr tok
pretty (Node (TimingLiteral _ tok) [] _) = tokenStr tok
pretty (Node (HardwareQubit _ tok) [] _) = tokenStr tok
pretty (Node ArrayInitExpr elems _) = "{" ++ prettyListElements elems ++ "}"
pretty (Node SetInitExpr elems _) = "{" ++ prettyListElements elems ++ "}"
pretty (Node RangeInitExpr [begin, step, end] _) =
  prettyMaybe "" begin "" ++ ":" ++ prettyMaybe "" step ":" ++ prettyMaybe "" end ""
pretty (Node DimExpr [size] _) = "#dim=" ++ pretty size
pretty (Node MeasureExpr [gateOp] _) = "measure " ++ pretty gateOp
pretty (Node IndexedIdentifier [ident, index] _) = pretty ident ++ "[" ++ prettyIndex index ++ "]"
pretty (Node InvGateModifier [] _) = "inv @"
pretty (Node PowGateModifier [expr] _) = "pow(" ++ pretty expr ++ ") @"
pretty (Node CtrlGateModifier [maybeExpr] _) = "ctrl " ++ prettyMaybe "(" maybeExpr ") " ++ "@"
pretty (Node NegCtrlGateModifier [maybeExpr] _) = "negctrl " ++ prettyMaybe "(" maybeExpr ") " ++ "@"
pretty (Node BitTypeSpec [maybeSize] _) = "bit" ++ prettyMaybeDsgn maybeSize
pretty (Node CregTypeSpec [maybeSize] _) = "creg" ++ prettyMaybeDsgn maybeSize
pretty (Node QregTypeSpec [maybeSize] _) = "qreg" ++ prettyMaybeDsgn maybeSize
pretty (Node IntTypeSpec [maybeSize] _) = "int" ++ prettyMaybeDsgn maybeSize
pretty (Node UintTypeSpec [maybeSize] _) = "uint" ++ prettyMaybeDsgn maybeSize
pretty (Node FloatTypeSpec [maybeSize] _) = "float" ++ prettyMaybeDsgn maybeSize
pretty (Node AngleTypeSpec [maybeSize] _) = "angle" ++ prettyMaybeDsgn maybeSize
pretty (Node BoolTypeSpec [] _) = "bool"
pretty (Node DurationTypeSpec [] _) = "duration"
pretty (Node StretchTypeSpec [] _) = "stretch"
pretty (Node ComplexTypeSpec [maybeSclr] _) = "complex" ++ prettyMaybeDsgn maybeSclr
pretty (Node QubitTypeSpec [maybeSize] _) = "qubit" ++ prettyMaybeDsgn maybeSize
pretty (Node ArrayTypeSpec (sclrType : exprs) _) =
  "array[" ++ pretty sclrType ++ ", " ++ prettyListElements exprs ++ "]"
pretty (Node ReadonlyArrayRefTypeSpec [sclrType, exprs@(Node List _ _)] _) =
  "readonly array[" ++ pretty sclrType ++ ", " ++ prettyList exprs ++ "]"
pretty (Node MutableArrayRefTypeSpec [sclrType, exprs@(Node List _ _)] _) =
  "mutable array[" ++ pretty sclrType ++ ", " ++ prettyList exprs ++ "]"
pretty (Node ReadonlyArrayRefTypeSpec [sclrType, dimExpr@(Node DimExpr _ _)] _) =
  "readonly array[" ++ pretty sclrType ++ ", " ++ pretty dimExpr ++ "]"
pretty (Node MutableArrayRefTypeSpec [sclrType, dimExpr@(Node DimExpr _ _)] _) =
  "mutable array[" ++ pretty sclrType ++ ", " ++ pretty dimExpr ++ "]"
pretty (Node (DefcalTarget tgt _) [] _) = tgt -- "measure", "reset", "delay", or some other identifier
-- does not handle CREG, QREG args (postfix size designator)
pretty (Node ArgumentDefinition [anyType, ident] _) = pretty anyType ++ " " ++ pretty ident
{- Error cases -}
-- Should have been handled above -- usually implies some change to how the surrounding renders
pretty NilNode = error "Unhandled NilNode for pretty"
-- Should have been handled above -- we can't know which separator to use
pretty (Node List elems _) = error ("Unhandled List node for pretty with children: " ++ show (map pretty elems))
-- Fallback
pretty (Node tag elems _) = error ("Missing pattern for pretty: Node " ++ show tag ++ " " ++ show (map pretty elems))

-- The syntax tree is as close to canonicalized as the tree easily gets
normalizeParens :: Node Tag c -> Node Tag c
normalizeParens NilNode = NilNode
-- Strip extra parens
normalizeParens (Node ParenExpr [expr] _) = normalizeParens expr
normalizeParens (Node ParenExpr children _) = undefined
-- Parenthesize nontrivial expressions associated with index operators
normalizeParens (Node IndexExpr [expr, list] ctx) =
  Node IndexExpr [parenthesizeNonTrivialExpr $ normalizeParens expr, normalizeParens list] ctx
normalizeParens (Node IndexExpr children _) = undefined
-- Parenthesize nontrivial expressions associated with other unary operators
normalizeParens (Node unop@(UnaryOperatorExpr _) [expr] ctx) =
  Node unop [parenthesizeNonTrivialExpr $ normalizeParens expr] ctx
normalizeParens (Node (UnaryOperatorExpr _) children _) = undefined
-- Parenthesize nontrivial expressions associated with binary operators
normalizeParens (Node binop@(BinaryOperatorExpr _) [exprA, exprB] ctx) =
  Node binop [parenthesizeNonTrivialExpr $ normalizeParens exprA, parenthesizeNonTrivialExpr $ normalizeParens exprB] ctx
normalizeParens (Node (BinaryOperatorExpr _) children _) = undefined
-- Pass everything else through untouched
normalizeParens (Node tag children ctx) = Node tag (map normalizeParens children) ctx

parenthesizeNonTrivialExpr :: Node Tag c -> Node Tag c
parenthesizeNonTrivialExpr expr =
  if isTrivialExpr expr then expr else Node ParenExpr [expr] (context expr)
  where
    isTrivialExpr (Node ParenExpr _ _) = True
    isTrivialExpr (Node CastExpr _ _) = True
    isTrivialExpr (Node DurationOfExpr _ _) = True
    isTrivialExpr (Node CallExpr _ _) = True
    isTrivialExpr (Node (Identifier _ _) [] _) = True
    isTrivialExpr (Node (IntegerLiteral _ _) [] _) = True
    isTrivialExpr (Node (FloatLiteral _ _) [] _) = True
    isTrivialExpr (Node (ImaginaryLiteral _ _) [] _) = True
    isTrivialExpr (Node (BooleanLiteral _ _) [] _) = True
    isTrivialExpr (Node (BitstringLiteral _ _) [] _) = True
    isTrivialExpr (Node (TimingLiteral _ _) [] _) = True
    isTrivialExpr (Node (HardwareQubit _ _) [] _) = True
    isTrivialExpr (Node ArrayInitExpr _ _) = True
    isTrivialExpr (Node SetInitExpr _ _) = True
    isTrivialExpr _ = False

-- Utility functions

tokenIdentifierName :: Token -> String
tokenIdentifierName (IdentifierToken str) = str
tokenIdentifierName (AnnotationKeywordToken ('@' : str)) = str
tokenIdentifierName (AnnotationKeywordToken str) = str

tokenIntegerVal :: Token -> Integer
tokenIntegerVal tok =
  case tok of
    BinaryIntegerLiteralToken str -> error "Unimplemented" -- readLiteral readBin $ stripPrefix 'b' str
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

prettyIndex :: Node Tag c -> String
prettyIndex idx = if tag idx == List then prettyList idx else pretty idx

prettyList :: Node Tag c -> String
prettyList NilNode = ""
prettyList (Node List elems _) = prettyListElements elems

prettyMaybeDsgn :: Node Tag c -> String
prettyMaybeDsgn expr = prettyMaybe "[" expr "]"

prettyMaybeList :: String -> Node Tag c -> String -> String
prettyMaybeList _ NilNode _ = ""
prettyMaybeList pre (Node List elems _) post = pre ++ prettyListElements elems ++ post

prettyMaybe :: String -> Node Tag c -> String -> String
prettyMaybe _ NilNode _ = ""
prettyMaybe pre expr post = pre ++ pretty expr ++ post

prettyListElements :: [Node Tag c] -> String
prettyListElements elems = intercalate ", " (map pretty elems)

prettyReturnType :: Node Tag c -> String
prettyReturnType NilNode = ""
prettyReturnType returnType = " -> " ++ pretty returnType

indent :: String -> String
indent block = concatMap (\s -> "  " ++ s ++ "\n") $ lines block

withContext :: c -> Node t () -> Node t c
withContext _ NilNode = NilNode
withContext ctx (Node t children _) = Node t (map (withContext ctx) children) ctx

node :: t -> [Node t ()] -> Node t ()
node tag children = Node {tag = tag, children = children, context = ()}

programNode :: Maybe Int -> Maybe Int -> [Node Tag ()] -> Node Tag ()
programNode (Just maj) (Just min) =
  node (Program maj (Just min) (VersionSpecifierToken (show maj ++ "." ++ show min)))
programNode (Just maj) Nothing = node (Program maj Nothing (VersionSpecifierToken $ show maj))
programNode Nothing Nothing = node (Program 3 Nothing EofToken)

stmtNode :: Tag -> [Node Tag ()] -> Node Tag ()
stmtNode tag children = node Statement [node tag children]

withAnnotations :: Node Tag () -> [Node Tag ()] -> Node Tag ()
withAnnotations (Node {tag = Statement, children = [stmtNode]}) annotations =
  node Statement $ stmtNode : annotations

binOpNode :: Token -> Node Tag () -> Node Tag () -> Node Tag ()
binOpNode op left right = node (BinaryOperatorExpr op) [left, right]

unOpNode :: Token -> Node Tag () -> Node Tag ()
unOpNode op inner = node (UnaryOperatorExpr op) [inner]

identifierNode :: String -> Node Tag ()
identifierNode name = node (Identifier {identifierName = name, identifierTok = IdentifierToken name}) []

integerLiteralNode :: Integer -> Node Tag ()
-- TODO there are edge cases where "show num" probably fails -- negative numbers? oversize?
integerLiteralNode val =
  node (IntegerLiteral {integerVal = val, integerTok = DecimalIntegerLiteralToken (show val)}) []

floatLiteralNode :: Double -> Node Tag ()
-- TODO "show num" probably compatible enough but this should be checked
floatLiteralNode val =
  node (FloatLiteral {floatVal = val, floatTok = FloatLiteralToken (show val)}) []

imaginaryLiteralNode :: Double -> Node Tag ()
imaginaryLiteralNode val =
  node (ImaginaryLiteral {imaginaryVal = val, imaginaryTok = ImaginaryLiteralToken (show val ++ "im")}) []

booleanLiteralNode :: Bool -> Node Tag ()
booleanLiteralNode val =
  node (BooleanLiteral {booleanVal = val, booleanTok = BooleanLiteralToken (if val then "true" else "false")}) []

bitstringLiteralNode :: [Bool] -> Node Tag ()
bitstringLiteralNode val =
  node
    ( BitstringLiteral
        { bitstringVal = val,
          bitstringTok = BitstringLiteralToken $ '"' : map (\b -> if b then '1' else '0') val ++ "\""
        }
    )
    []
