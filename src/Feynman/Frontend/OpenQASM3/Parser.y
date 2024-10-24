{
module Feynman.Frontend.OpenQASM3.Parser (parseQasm3, parseString) where

import Control.Monad (mplus)
import Data.Char
import Debug.Trace (trace)
import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import Feynman.Frontend.OpenQASM3.Lexer (Lexeme(..))
import qualified Feynman.Frontend.OpenQASM3.Lexer as L
import Feynman.Frontend.OpenQASM3.Syntax

}
-- This grammar was directly adapted from the official OpenQASM3 grammar from grammar/index.html

%name parseQasm3 program

%tokentype { Lexeme }
%error { parseError }
%monad { L.Alex } { >>= } { pure }
%lexer { lexer } { Lexeme _ EofToken }

%token
    OPENQASM                                { Lexeme _ OpenqasmToken }
    INCLUDE                                 { Lexeme _ IncludeToken }
    DEFCALGRAMMAR                           { Lexeme _ DefcalgrammarToken }
    DEF                                     { Lexeme _ DefToken }
    CAL                                     { Lexeme _ CalToken }
    DEFCAL                                  { Lexeme _ DefcalToken }
    GATE                                    { Lexeme _ GateToken }
    EXTERN                                  { Lexeme _ ExternToken }
    BOX                                     { Lexeme _ BoxToken }
    LET                                     { Lexeme _ LetToken }
    BREAK                                   { Lexeme _ BreakToken }
    CONTINUE                                { Lexeme _ ContinueToken }
    IF                                      { Lexeme _ IfToken }
    ELSE                                    { Lexeme _ ElseToken }
    END                                     { Lexeme _ EndToken }
    RETURN                                  { Lexeme _ ReturnToken }
    FOR                                     { Lexeme _ ForToken }
    WHILE                                   { Lexeme _ WhileToken }
    IN                                      { Lexeme _ InToken }
    PRAGMA                                  { Lexeme _ PragmaToken }
    AnnotationKeyword                       { Lexeme _ (AnnotationKeywordToken _) }
    INPUT                                   { Lexeme _ InputToken }
    OUTPUT                                  { Lexeme _ OutputToken }
    CONST                                   { Lexeme _ ConstToken }
    READONLY                                { Lexeme _ ReadonlyToken }
    MUTABLE                                 { Lexeme _ MutableToken }
    QREG                                    { Lexeme _ QregToken }
    QUBIT                                   { Lexeme _ QubitToken }
    CREG                                    { Lexeme _ CregToken }
    BOOL                                    { Lexeme _ BoolToken }
    BIT                                     { Lexeme _ BitToken }
    INT                                     { Lexeme _ IntToken }
    UINT                                    { Lexeme _ UintToken }
    FLOAT                                   { Lexeme _ FloatToken }
    ANGLE                                   { Lexeme _ AngleToken }
    COMPLEX                                 { Lexeme _ ComplexToken }
    ARRAY                                   { Lexeme _ ArrayToken }
    -- VOID                                    { Lexeme _ VoidToken }
    DURATION                                { Lexeme _ DurationToken }
    STRETCH                                 { Lexeme _ StretchToken }
    GPHASE                                  { Lexeme _ GphaseToken }
    INV                                     { Lexeme _ InvToken }
    POW                                     { Lexeme _ PowToken }
    CTRL                                    { Lexeme _ CtrlToken }
    NEGCTRL                                 { Lexeme _ NegctrlToken }
    DIM                                     { Lexeme _ DimToken }
    DURATIONOF                              { Lexeme _ DurationofToken }
    DELAY                                   { Lexeme _ DelayToken }
    RESET                                   { Lexeme _ ResetToken }
    MEASURE                                 { Lexeme _ MeasureToken }
    BARRIER                                 { Lexeme _ BarrierToken }
    BooleanLiteral                          { Lexeme _ (BooleanLiteralToken _) }
    LBRACKET                                { Lexeme _ LbracketToken }
    RBRACKET                                { Lexeme _ RbracketToken }
    LBRACE                                  { Lexeme _ LbraceToken }
    RBRACE                                  { Lexeme _ RbraceToken }
    LPAREN                                  { Lexeme _ LparenToken }
    RPAREN                                  { Lexeme _ RparenToken }
    COLON                                   { Lexeme _ ColonToken }
    SEMICOLON                               { Lexeme _ SemicolonToken }
    -- DOT                                     { Lexeme _ DotToken }
    COMMA                                   { Lexeme _ CommaToken }
    EQUALS                                  { Lexeme _ EqualsToken }
    ARROW                                   { Lexeme _ ArrowToken }
    PLUS                                    { Lexeme _ PlusToken }
    DOUBLE_PLUS                             { Lexeme _ DoublePlusToken }
    MINUS                                   { Lexeme _ MinusToken }
    ASTERISK                                { Lexeme _ AsteriskToken }
    DOUBLE_ASTERISK                         { Lexeme _ DoubleAsteriskToken }
    SLASH                                   { Lexeme _ SlashToken }
    PERCENT                                 { Lexeme _ PercentToken }
    PIPE                                    { Lexeme _ PipeToken }
    DOUBLE_PIPE                             { Lexeme _ DoublePipeToken }
    AMPERSAND                               { Lexeme _ AmpersandToken }
    DOUBLE_AMPERSAND                        { Lexeme _ DoubleAmpersandToken }
    CARET                                   { Lexeme _ CaretToken }
    AT                                      { Lexeme _ AtToken }
    TILDE                                   { Lexeme _ TildeToken }
    EXCLAMATION_POINT                       { Lexeme _ ExclamationPointToken }
    -- EqualityOperator
    DOUBLE_EQUALS                           { Lexeme _ DoubleEqualsToken }
    EXCLAMATION_POINT_EQUALS                { Lexeme _ ExclamationPointEqualsToken }
    -- CompoundAssignmentOperator
    PLUS_EQUALS                             { Lexeme _ PlusEqualsToken }
    MINUS_EQUALS                            { Lexeme _ MinusEqualsToken }
    ASTERISK_EQUALS                         { Lexeme _ AsteriskEqualsToken }
    SLASH_EQUALS                            { Lexeme _ SlashEqualsToken }
    AMPERSAND_EQUALS                        { Lexeme _ AmpersandEqualsToken }
    PIPE_EQUALS                             { Lexeme _ PipeEqualsToken }
    TILDE_EQUALS                            { Lexeme _ TildeEqualsToken }
    CARET_EQUALS                            { Lexeme _ CaretEqualsToken }
    DOUBLE_LESS_EQUALS                      { Lexeme _ DoubleLessEqualsToken }
    DOUBLE_GREATER_EQUALS                   { Lexeme _ DoubleGreaterEqualsToken }
    PERCENT_EQUALS                          { Lexeme _ PercentEqualsToken }
    DOUBLE_ASTERISK_EQUALS                  { Lexeme _ DoubleAsteriskEqualsToken }
    -- ComparisonOperator
    LESS                                    { Lexeme _ LessToken }
    GREATER                                 { Lexeme _ GreaterToken }
    LESS_EQUALS                             { Lexeme _ LessEqualsToken }
    GREATER_EQUALS                          { Lexeme _ GreaterEqualsToken }
    -- BitshiftOperator
    DOUBLE_LESS                             { Lexeme _ DoubleLessToken }
    DOUBLE_GREATER                          { Lexeme _ DoubleGreaterToken }
    --
    ImaginaryLiteral                        { Lexeme _ (ImaginaryLiteralToken _) }
    BinaryIntegerLiteral                    { Lexeme _ (BinaryIntegerLiteralToken _) }
    OctalIntegerLiteral                     { Lexeme _ (OctalIntegerLiteralToken _) }
    DecimalIntegerLiteral                   { Lexeme _ (DecimalIntegerLiteralToken _) }
    HexIntegerLiteral                       { Lexeme _ (HexIntegerLiteralToken _) }
    Identifier                              { Lexeme _ (IdentifierToken _) }
    HardwareQubit                           { Lexeme _ (HardwareQubitToken _) }
    FloatLiteral                            { Lexeme _ (FloatLiteralToken _) }
    TimingLiteral                           { Lexeme _ (TimingLiteralToken _) }
    BitstringLiteral                        { Lexeme _ (BitstringLiteralToken _) }
    -- Whitespace                              { Lexeme _ (WhitespaceToken _) }
    -- Newline                                 { Lexeme _ (NewlineToken _) }
    -- LineComment                             { Lexeme _ (LineCommentToken _) }
    -- BlockComment                            { Lexeme _ (BlockCommentToken _) }
    VersionSpecifier                        { Lexeme _ (VersionSpecifierToken _) }
    StringLiteral                           { Lexeme _ (StringLiteralToken _) }
    RemainingLineContent                    { Lexeme _ (RemainingLineContentToken _) }
    CalibrationBlock                        { Lexeme _ (CalibrationBlockToken _) }


-- Specify binary operator associativity and precedence: lower precedence first (opposite to ANTLR)

%nonassoc FOR
%nonassoc THEN
%nonassoc ELSE

-- %left CompoundAssignmentOperator -- assignmentExpression
%left PLUS_EQUALS MINUS_EQUALS ASTERISK_EQUALS SLASH_EQUALS
      AMPERSAND_EQUALS PIPE_EQUALS TILDE_EQUALS CARET_EQUALS
      DOUBLE_LESS_EQUALS DOUBLE_GREATER_EQUALS PERCENT_EQUALS
      DOUBLE_ASTERISK_EQUALS

%left DOUBLE_PIPE             -- logicalOrExpression
%left DOUBLE_AMPERSAND        -- logicalAndExpression
%left PIPE                    -- bitwiseOrExpression
%left CARET                   -- bitwiseXorExpression
%left AMPERSAND               -- bitwiseAndExpression

-- %left EqualityOperator        -- equalityExpression
%left DOUBLE_EQUALS EXCLAMATION_POINT_EQUALS
-- %left ComparisonOperator      -- comparisonExpression
%left LESS GREATER LESS_EQUALS GREATER_EQUALS
-- %left BitshiftOperator        -- bitshiftExpression
%left DOUBLE_LESS DOUBLE_GREATER

%left PLUS MINUS              -- additiveExpression
%left ASTERISK SLASH PERCENT  -- multiplicativeExpression
%left TILDE EXCLAMATION_POINT UNARY_MINUS
%right DOUBLE_ASTERISK        -- powerExpression
%left LBRACKET RBRACKET LPAREN RPAREN

%nonassoc RVALUE_INDEX
%nonassoc LVALUE_INDEX


%%


program :: { ParseNode {- Program -} }
    : OPENQASM VersionSpecifier SEMICOLON many0(statementOrScope)
                                    { let tok = lexemeToken $2; (maj, min) = tokenVersionMajMin tok
                                       in Ast.Node (Program maj min tok) $4 (lsr $1) }
    | many0(statementOrScope)
                                    { Ast.Node (Program 3 Nothing EofToken) $1
                                               (srList $ map Ast.context $1) }

-- A statement is any valid single statement of an OpenQASM 3 program, with the
-- exception of the version-definition statement (which must be unique, and the
-- first statement of the file if present).  This file just defines rules for
-- parsing; we leave semantic analysis and rejection of invalid scopes for
-- compiler implementations.
statement :: { ParseNode {- Statement -} }
    : PRAGMA RemainingLineContent
                                    { let tok = lexemeToken $2
                                       in Ast.Node (Pragma (tokenStringVal tok) tok) [] (lsr $1) }
    | PRAGMA
                                    { Ast.Node (Pragma "" (RemainingLineContentToken "")) [] (lsr $1) }
    -- All the actual statements of the language.
    | many0(annotation) statementContent
                                    { Ast.Node Statement ($2 : $1) (srList $ map Ast.context ($1 ++ [$2])) }

annotation :: { ParseNode {- Annotation -} }
    : AnnotationKeyword RemainingLineContent
                                    { case ($1, $2) of
                                        (Lexeme sr kwt, Lexeme _ (RemainingLineContentToken c)) ->
                                          Ast.Node (Annotation (tokenIdentifierName kwt) c kwt) [] sr}
    | AnnotationKeyword
                                    { case $1 of Lexeme sr kwt ->
                                        Ast.Node (Annotation (tokenIdentifierName kwt) "" kwt) [] sr}

scope :: { ParseNode {- Statement -} }
    : LBRACE many0(statementOrScope) RBRACE
                                    { Ast.Node Scope $2 (lsr $1) }

statementOrScope :: { ParseNode {- Statement | Scope -} }
    : statement                     { $1 }
    | scope                         { $1 }


{- Start top-level statement definitions. -}

statementContent :: { ParseNode {- StatementContent -} }
-- Inclusion statements.
    : DEFCALGRAMMAR StringLiteral SEMICOLON
                                    { let tok = lexemeToken $2
                                       in Ast.Node (DefcalgrammarStmt (tokenStringVal tok) tok) [] (lsr $1) }
    | INCLUDE StringLiteral SEMICOLON
                                    { let tok = lexemeToken $2
                                       in Ast.Node (IncludeStmt (tokenStringVal tok) tok) [] (lsr $1) }

-- Control-flow statements.
    | BREAK SEMICOLON               { Ast.Node BreakStmt [] (lsr $1) }
    | CONTINUE SEMICOLON            { Ast.Node ContinueStmt [] (lsr $1) }
    | END SEMICOLON                 { Ast.Node EndStmt [] (lsr $1) }

    -- | FOR scalarType Identifier IN expression statementOrScope
    --                                 { ForStmt $1 $2 $3 $5 $6 }
    | FOR scalarType identifier IN lvalueExpression statement
                                    { Ast.Node ForStmt [$2, $3, toExpression $5, $6] (lsr $1) }
    | FOR scalarType identifier IN lvalueExpression scope
                                    { Ast.Node ForStmt [$2, $3, toExpression $5, $6] (lsr $1) }

    | FOR scalarType identifier IN LBRACKET rangeExpression RBRACKET statementOrScope
                                    { Ast.Node ForStmt [$2, $3, $6, $8] (lsr $1) }
    | FOR scalarType identifier IN setExpression statementOrScope
                                    { Ast.Node ForStmt [$2, $3, $5, $6] (lsr $1) }
    | IF LPAREN expression RPAREN statementOrScope ifElseClause
                                    { Ast.Node IfStmt [$3, $5, $6] (lsr $1) }

    | RETURN opt(measureExpression) SEMICOLON
                                    { Ast.Node ReturnStmt [$2] (lsr $1) }
    | WHILE LPAREN expression RPAREN statementOrScope
                                    { Ast.Node WhileStmt [$3, $5] (lsr $1) }

-- Quantum directive statements.
    | BARRIER list0(gateOperand) SEMICOLON
                                    { Ast.Node BarrierStmt $2 (lsr $1) }
    | BOX opt(designator) scope     { Ast.Node BoxStmt [$2, $3] (lsr $1) }
    | DELAY designator list0(gateOperand) SEMICOLON
                                    { Ast.Node DelayStmt ($2 : $3) (lsr $1) }

{- 'gateCallStatement'  is split in two to avoid a potential ambiguity with an
 - 'expressionStatement' that consists of a single function call.  The only
 - "gate" that can have no operands is 'gphase' with no control modifiers, and
 - 'gphase(pi);' looks grammatically identical to 'fn(pi);'.  We disambiguate by
 - having 'gphase' be its own token, and requiring that all other gate calls
 - grammatically have at least one qubit.  Strictly, as long as 'gphase' is a
 - separate token, ANTLR can disambiguate the statements by the definition
 - order, but this is more robust. -}

    -- Original ANTLR grammar:
    -- gateModifierList Identifier ((LPAREN) expressionList (RPAREN))? designator? gateOperandList? (SEMICOLON)

    -- My naive translation:
    -- | many(gateModifier) Identifier optList(LPAREN, list0(expression), RPAREN) opt(designator) list1(gateOperand) SEMICOLON
    --                                 { GateCallStmt $1 $2 (fromMaybe [] $3) $4 $5 }
    -- | many(gateModifier) GPHASE optList(LPAREN, list0(expression), RPAREN) opt(designator) list0(gateOperand) SEMICOLON
    --                                 { GateCallStmt $1 $2 (fromMaybe [] $3) $4 $5 }

    -- The rules are further subdivided because having a zero-length production
    -- at the start of these rules prevents them from being merged with rules
    -- that share a common prefix (i.e., the Expression and AssignmentStmt rules
    -- below, both of which can start with Identifier). Without going into too
    -- much detail, the problem is that without arbitrary lookahead, when the
    -- parser encounters the "Identifier" token, it can't decide whether to
    -- produce a zero-length gateModifier list before it, i.e., it has to
    -- decide right then whether it's generating a GateCallStmt or Expression. If
    -- there's a rule for GateCallStmt that doesn't include the zero-length
    -- gateModifier list, then it can carry on reading tokens for a while
    -- longer before it decides which rule to reduce.

    -- TODO the designator, which we don't currently record, is for durations.

    | many1(gateModifier) GPHASE optList(LPAREN, list0(expression), RPAREN) list0(gateOperand) SEMICOLON
                                    { Ast.Node GateCallStmt
                                        [mkList $1 Ast.NilRef, mkIdentifier $2, $3, Ast.NilNode, mkList $4 (lsr $5)]
                                        (Ast.context $ head $1) }
    | many1(gateModifier) identifier LPAREN list0(expression) RPAREN list1(gateOperand) SEMICOLON
                                    { Ast.Node GateCallStmt
                                        [ mkList $1 Ast.NilRef, $2, mkList $4 (lsr $3), Ast.NilNode,
                                          mkList $6 Ast.NilRef
                                        ]
                                        (Ast.context $ head $1) }
    | many1(gateModifier) identifier list1(gateOperand) SEMICOLON
                                    { Ast.Node GateCallStmt
                                        [mkList $1 Ast.NilRef, $2, Ast.NilNode, Ast.NilNode, mkList $3 Ast.NilRef]
                                        (Ast.context $ head $1) }

    | GPHASE optList(LPAREN, list0(expression), RPAREN) list0(gateOperand) SEMICOLON
                                    { Ast.Node GateCallStmt
                                        [Ast.NilNode, mkIdentifier $1, $2, Ast.NilNode, mkList $3 (lsr $4)]
                                        (lsr $1) }
    | expression LPAREN list0(expression) RPAREN list1(gateOperand) SEMICOLON
                                    { Ast.Node GateCallStmt
                                        [Ast.NilNode, $1, mkList $3 (lsr $2), Ast.NilNode, mkList $5 Ast.NilRef]
                                        (Ast.context $1) }
    | expression list1(gateOperand) SEMICOLON %prec RVALUE_INDEX
                                    { Ast.Node GateCallStmt
                                        [Ast.NilNode, $1, Ast.NilNode, Ast.NilNode, mkList $2 Ast.NilRef]
                                        (Ast.context $1) }

-- Non-declaration assignments and calculations.
    | expression assignmentOperator measureExpression SEMICOLON
                                    { Ast.Node (AssignmentStmt $ lexemeToken $2) [$1, $3] (Ast.context $1) }

    | expression SEMICOLON          { Ast.Node ExpressionStmt [$1] (Ast.context $1) }

-- measureArrowAssignmentStatement also permits the case of not assigning the
-- result to any classical value too.
    | MEASURE gateOperand opt(measureArrowTarget) SEMICOLON
                                    { Ast.Node MeasureArrowAssignmentStmt
                                        [Ast.Node MeasureExpr [$2] (lsr $1), $3]
                                        (lsr $1) }
    | RESET gateOperand SEMICOLON   { Ast.Node ResetStmt [$2] (lsr $1) }

-- Primitive declaration statements.
    | LET identifier EQUALS aliasExpression SEMICOLON
                                    { Ast.Node AliasDeclStmt ($2 : $4) (lsr $1) }
    | scalarOrArrayType identifier opt(declarationExpression) SEMICOLON
                                    { Ast.Node ClassicalDeclStmt [$1, $2, $3] (Ast.context $1) }
    | CONST scalarType identifier declarationExpression SEMICOLON
                                    { Ast.Node ConstDeclStmt [$2, $3, $4] (lsr $1) }
    | INPUT scalarOrArrayType identifier SEMICOLON
                                    { Ast.Node InputIoDeclStmt [$2, $3] (lsr $1) }
    | OUTPUT scalarOrArrayType identifier SEMICOLON
                                    { Ast.Node OutputIoDeclStmt [$2, $3] (lsr $1) }
    | CREG identifier opt(designator) SEMICOLON
                                    { Ast.Node CregOldStyleDeclStmt [$2, $3] (lsr $1) }
    | QREG identifier opt(designator) SEMICOLON
                                    { Ast.Node QregOldStyleDeclStmt [$2, $3] (lsr $1) }
    | qubitType identifier SEMICOLON
                                    { Ast.Node QuantumDeclStmt [$1, $2] (Ast.context $1) }

-- Declarations and definitions of higher-order objects.
    | DEF identifier LPAREN list0(argumentDefinition) RPAREN opt(returnSignature) scope
                                    { Ast.Node DefStmt [$2, mkList $4 (lsr $3), $6, $7] (lsr $1) }
    | EXTERN identifier LPAREN list0(externArgument) RPAREN opt(returnSignature) SEMICOLON
                                    { Ast.Node ExternStmt [$2, mkList $4 (lsr $3), $6] (lsr $1) }
    | GATE identifier optList(LPAREN, list0(identifier), RPAREN) list0(identifier) scope
                                    { Ast.Node GateStmt [$2, $3, mkList $4 (Ast.context $5), $5]
                                        (lsr $1) }

-- Statements where the bulk is in the calibration language.
    | CAL calibrationBlock
                                    { Ast.Node (CalStmt $ lexemeToken $2) [] (lsr $1) }
    | DEFCAL defcalTarget optList(LPAREN, list0(defcalArgumentDefinition), RPAREN) list0(defcalOperand)
        opt(returnSignature) calibrationBlock
                                    { Ast.Node DefcalStmt
                                        [ $2, $3, mkList $4 (lsr $1), $5,
                                          Ast.Node (CalStmt $ lexemeToken $6) [] (lsr $6)]
                                        (lsr $1) }

assignmentOperator :: { Lexeme }
    : EQUALS                        { $1 }
    | PLUS_EQUALS                   { $1 }
    | MINUS_EQUALS                  { $1 }
    | ASTERISK_EQUALS               { $1 }
    | SLASH_EQUALS                  { $1 }
    | AMPERSAND_EQUALS              { $1 }
    | PIPE_EQUALS                   { $1 }
    | TILDE_EQUALS                  { $1 }
    | CARET_EQUALS                  { $1 }
    | DOUBLE_LESS_EQUALS            { $1 }
    | DOUBLE_GREATER_EQUALS         { $1 }
    | PERCENT_EQUALS                { $1 }
    | DOUBLE_ASTERISK_EQUALS        { $1 }

ifElseClause :: { ParseNode {- StatementOrScope -} }
    : %prec THEN                    { Ast.NilNode }
    | ELSE statementOrScope         { $2 }

measureArrowTarget :: { ParseNode {- IndexedIdentifier -} }
    : ARROW lvalueExpression        { $2 }

scalarOrArrayType :: { ParseNode {- ScalarOrArrayType -} }
    : scalarType                    { $1 }
    | arrayType                     { $1 }

calibrationBlock :: { Lexeme }
    : LBRACE many0(calibrationBlock) RBRACE
                                    { Lexeme (lsr $1) $ CalibrationBlockToken
                                        ('{' : concatMap (tokenStringVal . lexemeToken) $2 ++ "}") }
    | CalibrationBlock              { $1 }

{- End top-level statement definitions. -}


{- Start expression definitions. -}

-- Operator precedence is resolved in the top section of the Happy definition.
expression :: { ParseNode {- Expression -} }
    : LPAREN expression RPAREN      { $2 }
    | expression DOUBLE_PIPE expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression DOUBLE_AMPERSAND expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression PIPE expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression CARET expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression AMPERSAND expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression DOUBLE_EQUALS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression EXCLAMATION_POINT_EQUALS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression LESS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression GREATER expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression LESS_EQUALS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression GREATER_EQUALS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression DOUBLE_LESS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression DOUBLE_GREATER expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression PLUS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression MINUS expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression ASTERISK expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression SLASH expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression PERCENT expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | expression DOUBLE_ASTERISK expression
                                    { mkBinaryOperatorExpr $1 $2 $3 }
    | TILDE expression              { mkUnaryOperatorExpr $1 $2 }
    | EXCLAMATION_POINT expression  { mkUnaryOperatorExpr $1 $2 }
    | MINUS expression %prec UNARY_MINUS
                                    { mkUnaryOperatorExpr $1 $2 }
    | expression indexExpr %prec RVALUE_INDEX
                                    { Ast.Node IndexExpr [$1, $2] (Ast.context $1) }
    | lvalueExpression %prec LVALUE_INDEX
                                    { toExpression $1 }
    | scalarOrArrayType LPAREN expression RPAREN
                                    { Ast.Node CastExpr [$1, $3] (Ast.context $1) }
    | DURATIONOF LPAREN scope RPAREN
                                    { Ast.Node DurationOfExpr [$3] (lsr $1) }
    | expression LPAREN list0(expression) RPAREN
                                    { Ast.Node CallExpr [$1, mkList $3 (lsr $2)] (Ast.context $1) }
    | BinaryIntegerLiteral          { let tok = lexemeToken $1
                                       in Ast.Node (IntegerLiteral (tokenIntegerVal tok) tok) [] (lsr $1) }
    | OctalIntegerLiteral           { let tok = lexemeToken $1
                                       in Ast.Node (IntegerLiteral (tokenIntegerVal tok) tok) [] (lsr $1) }
    | DecimalIntegerLiteral         { let tok = lexemeToken $1
                                       in Ast.Node (IntegerLiteral (tokenIntegerVal tok) tok) [] (lsr $1) }
    | HexIntegerLiteral             { let tok = lexemeToken $1
                                       in Ast.Node (IntegerLiteral (tokenIntegerVal tok) tok) [] (lsr $1) }
    | FloatLiteral                  { let tok = lexemeToken $1
                                       in Ast.Node (FloatLiteral (tokenFloatVal tok) tok) [] (lsr $1) }
    | ImaginaryLiteral              { let tok = lexemeToken $1
                                       in Ast.Node (ImaginaryLiteral (tokenFloatVal tok) tok) [] (lsr $1) }
    | BooleanLiteral                { let tok = lexemeToken $1
                                       in Ast.Node (BooleanLiteral (tokenBooleanVal tok) tok) [] (lsr $1) }
    | BitstringLiteral              { let tok = lexemeToken $1
                                       in Ast.Node (BitstringLiteral (tokenBitstringVal tok) tok) [] (lsr $1) }
    | TimingLiteral                 { let tok = lexemeToken $1
                                       in Ast.Node (TimingLiteral (tokenTimingVal tok) tok) [] (lsr $1) }
    | HardwareQubit                 { let tok = lexemeToken $1
                                       in Ast.Node (HardwareQubit (tokenHwQubitIndex tok) tok) [] (lsr $1) }


-- Special-case expressions that are only valid in certain contexts.  These are
-- not in the expression tree, but can contain elements that are within it.
aliasExpression :: { [ParseNode] {- AliasExpression -} }
    : listSep1(DOUBLE_PLUS, expression)
                                    { $1 }

declarationExpression :: { ParseNode {- DeclarationExpressionNode -} }
    : EQUALS arrayLiteral           { $2 }
    | EQUALS measureExpression      { $2 }

measureExpression :: { ParseNode {- MeasureExpression -} }
    : expression                    { $1 }
    | MEASURE gateOperand           { Ast.Node MeasureExpr [$2] (lsr $1) }

rangeOrExpressionIndex :: { ParseNode {- RangeOrExpressionIndex -} }
    : expression                    { $1 }
    | rangeExpression               { $1 }

rangeExpression :: { ParseNode {- RangeExpression -} }
    : opt(expression) COLON opt(expression) COLON opt(expression)
                                    { Ast.Node RangeInitExpr [$1, $3, $5] (srList [Ast.context $1, lsr $2]) }
    | opt(expression) COLON opt(expression)
                                    { Ast.Node RangeInitExpr [$1, Ast.NilNode, $3] (srList [Ast.context $1, lsr $2]) }

setExpression :: { ParseNode {- SetExpression -} }
    : LBRACE list0(expression) RBRACE
                                    { Ast.Node SetInitExpr $2 (lsr $1) }

arrayLiteral :: { ParseNode {- ArrayLiteral -} }
    : LBRACE list0(arrayLiteralElement) RBRACE
                                    { Ast.Node ArrayInitExpr $2 (lsr $1) }

arrayLiteralElement :: { ParseNode {- ArrayLiteralElement -} }
    : expression                    { $1 }
    | arrayLiteral                  { $1 }

-- The general form is a comma-separated list of indexing entities.
-- 'setExpression' is only valid when being used as a single index: registers
-- can support it for creating aliases, but arrays cannot.
indexExpr :: { ParseNode {- IndexOperator -} }
    : LBRACKET setExpression RBRACKET
                                    { $2 }
    | LBRACKET list0(rangeOrExpressionIndex) RBRACKET
                                    { Ast.Node List $2 (lsr $1) }

-- Alternative form to 'indexExpression' for cases where an obvious l-value is
-- better grammatically than a generic expression.  Some current uses of this
-- rule may be better as 'expression', leaving the semantic analysis to later
-- (for example in gate calls).
lvalueExpression :: { ParseNode {- IndexedIdentifier -} }
    : identifier                    { $1 }
    | lvalueExpression indexExpr
                                    { Ast.Node IndexedIdentifier [$1, $2] (Ast.context $1) }

{- End expression definitions. -}


{- Start type definitions. -}

returnSignature :: { ParseNode {- ScalarType -} }
    : ARROW scalarType              { $2 }

gateModifier :: { ParseNode {- GateModifier -} }
    : INV AT                        { Ast.Node InvGateModifier [] (lsr $1) }
    | POW LPAREN expression RPAREN AT
                                    { Ast.Node PowGateModifier [$3] (lsr $1) }
    | CTRL opt3(LPAREN, expression, RPAREN) AT
                                    { Ast.Node CtrlGateModifier [$2] (lsr $1)}
    | NEGCTRL opt3(LPAREN, expression, RPAREN) AT
                                    { Ast.Node NegCtrlGateModifier [$2] (lsr $1) }

scalarType :: { ParseNode {- ScalarType -} }
    : BIT opt(designator)           { Ast.Node BitTypeSpec [$2] (lsr $1) }
    | INT opt(designator)           { Ast.Node IntTypeSpec [$2] (lsr $1) }
    | UINT opt(designator)          { Ast.Node UintTypeSpec [$2] (lsr $1) }
    | FLOAT opt(designator)         { Ast.Node FloatTypeSpec [$2] (lsr $1) }
    | ANGLE opt(designator)         { Ast.Node AngleTypeSpec [$2] (lsr $1) }
    | BOOL                          { Ast.Node BoolTypeSpec [] (lsr $1) }
    | DURATION                      { Ast.Node DurationTypeSpec [] (lsr $1) }
    | STRETCH                       { Ast.Node StretchTypeSpec [] (lsr $1) }
    | COMPLEX opt3(LBRACKET, scalarType, RBRACKET)
                                    { Ast.Node ComplexTypeSpec [$2] (lsr $1) }

qubitType :: { ParseNode {- QubitType -} }
    : QUBIT opt(designator)         { Ast.Node QubitTypeSpec [$2] (lsr $1) }

arrayType :: { ParseNode {- ArrayType -} }
    : ARRAY LBRACKET scalarType COMMA list0(expression) RBRACKET
                                    { Ast.Node ArrayTypeSpec ($3 : $5) (lsr $1) }

arrayReferenceType :: { ParseNode {- ArrayReferenceType -} }
    : READONLY ARRAY LBRACKET scalarType COMMA list0(expression) RBRACKET
                                    { Ast.Node ReadonlyArrayRefTypeSpec [$4, mkList $6 (lsr $5)] (lsr $1) }
    | MUTABLE ARRAY LBRACKET scalarType COMMA list0(expression) RBRACKET
                                    { Ast.Node MutableArrayRefTypeSpec [$4, mkList $6 (lsr $5)] (lsr $1) }
    | READONLY ARRAY LBRACKET scalarType COMMA DIM EQUALS expression RBRACKET
                                    { Ast.Node ReadonlyArrayRefTypeSpec [$4, Ast.Node DimExpr [$8] (lsr $6)] (lsr $1) }
    | MUTABLE ARRAY LBRACKET scalarType COMMA DIM EQUALS expression RBRACKET
                                    { Ast.Node MutableArrayRefTypeSpec [$4, Ast.Node DimExpr [$8] (lsr $6)] (lsr $1) }

{- Start miscellany. -}

-- TODO
designator :: { ParseNode {- Expression -} }
    : LBRACKET expression RBRACKET  { $2 }

defcalTarget :: { ParseNode {- DefcalTarget -} }
    : MEASURE                       { let tok = lexemeToken $1
                                       in Ast.Node (DefcalTarget (tokenStr tok) tok) [] (lsr $1) }
    | RESET                         { let tok = lexemeToken $1
                                       in Ast.Node (DefcalTarget (tokenStr tok) tok) [] (lsr $1) }
    | DELAY                         { let tok = lexemeToken $1
                                       in Ast.Node (DefcalTarget (tokenStr tok) tok) [] (lsr $1) }
    | identifier                    { $1 }

defcalArgumentDefinition :: { ParseNode {- DefcalArgumentDefinition -} }
    : expression                    { $1 }
    | argumentDefinition            { $1 }

defcalOperand :: { ParseNode {- DefcalOperand -} }
    : identifier                    { $1 }
    | hardwareQubit                 { $1 }

gateOperand :: { ParseNode {- GateOperand -} }
    : lvalueExpression              { $1 }
    | hardwareQubit                 { $1 }

externArgument :: { ParseNode {- ExternArgument -} }
    : scalarType                    { $1 }
    | arrayReferenceType            { $1 }
    | CREG opt(designator)          { Ast.Node CregTypeSpec [$2] (lsr $1) }

argumentDefinition :: { ParseNode {- ArgumentDefinition -} }
    : scalarType identifier         { Ast.Node ArgumentDefinition [$1, $2] (Ast.context $1) }
    | qubitType identifier          { Ast.Node ArgumentDefinition [$1, $2] (Ast.context $1) }
    | CREG identifier opt(designator)
                                    { Ast.Node ArgumentDefinition [Ast.Node CregTypeSpec [$3] (lsr $1), $2] (lsr $1) }
    | QREG identifier opt(designator)
                                    { Ast.Node ArgumentDefinition [Ast.Node QregTypeSpec [$3] (lsr $1), $2] (lsr $1) }
    | arrayReferenceType identifier { Ast.Node ArgumentDefinition [$1, $2] (Ast.context $1) }

identifier :: { ParseNode {- Identifier -} }
    : Identifier                    { let tok = lexemeToken $1
                                       in Ast.Node (Identifier (tokenIdentifierName tok) tok) [] (lsr $1) }

hardwareQubit :: { ParseNode {- HardwareQubit -} }
    : HardwareQubit                 { let tok = lexemeToken $1
                                       in Ast.Node (HardwareQubit (tokenHwQubitIndex tok) tok) [] (lsr $1) }

{- End miscellany. -}

{- End type definitions. -}


{- Start utility macros. -}

many0(p)
    :                               { [] }
    | manyRev1(p)                   { reverse $1 }

many1(p)
    : manyRev1(p)                   { reverse $1 }

manyRev1(p)
    : p                             { [$1] }
    | manyRev1(p) p                 { $2 : $1 }

list0(p)
    :                               { [] }
    | list1(p)                      { $1 }

-- Convention in this grammar is that comma-separated lists can have trailing commas.
list1(p)
    : p listSepRev(COMMA, p) COMMA
                                    { $1 : reverse $2 }
    | p listSepRev(COMMA, p)
                                    { $1 : reverse $2 }

listSep1(s, p)
    : p listSepRev(s, p)
                                    { $1 : reverse $2 }

listSepRev(s, p)
    :                               { [] }
    | listSepRev(s, p) s p          { $3 : $1 }

opt(p)
    :                               { Ast.NilNode }
    | p                             { $1 }

opt2(p, q)
    :                               { Ast.NilNode }
    | p q                           { $2 }

opt3(p, q, r)
    :                               { Ast.NilNode }
    | p q r                         { $2 }

optList(p, q, r)
    :                               { Ast.NilNode }
    | p q r                         { Ast.Node List $2 (lsr $1) }

{- End utility macros. -}

{
lsr :: Lexeme -> Ast.SourceRef
lsr = lexemeSource

srList :: [Ast.SourceRef] -> Ast.SourceRef
srList [] = Ast.NilRef
srList (sr : srs) = if sr == Ast.NilRef then srList srs else sr

mkBinaryOperatorExpr :: ParseNode -> Lexeme -> ParseNode -> ParseNode
mkBinaryOperatorExpr left op right = Ast.Node (BinaryOperatorExpr (lexemeToken op)) [left, right] (Ast.context left)

mkUnaryOperatorExpr :: Lexeme -> ParseNode -> ParseNode
mkUnaryOperatorExpr op expr = Ast.Node (UnaryOperatorExpr (lexemeToken op)) [expr] (lsr op)

mkList :: [ParseNode] -> Ast.SourceRef -> ParseNode
mkList [] fallbackRef = Ast.Node List [] fallbackRef
mkList children fallbackRef = Ast.Node List children (srList ((map Ast.context children) ++ [fallbackRef]))

mkIdentifier :: Lexeme -> ParseNode
mkIdentifier lex = let tok = lexemeToken lex in Ast.Node (Identifier (tokenStr tok) tok) [] (lsr lex)

toExpression :: ParseNode -> ParseNode
toExpression (Ast.Node IndexedIdentifier (ident : indices) ctx) =
  let wrap expr [] = expr
      wrap expr (idx : indices) = wrap (Ast.Node IndexExpr [expr, idx] ctx) indices
   in wrap ident (reverse indices)
toExpression node@(Ast.Node (Identifier _ _) _ _) = node
toExpression node | trace (show node) False = undefined

appendIndexExpr :: ParseNode -> [ParseNode] -> ParseNode
appendIndexExpr expr idx = expr {Ast.children = (Ast.children expr) ++ [mkList idx Ast.NilRef]}

parseError :: L.Lexeme -> L.Alex a
parseError lex = do
  (L.AlexPn _ line column, _, _, _) <- L.alexGetInput
  L.alexError $ "Parse error: " <> show (Ast.sourceLine $ L.lexemeSource lex) <>
                (case Ast.sourceColumn $ L.lexemeSource lex of
                   Nothing -> ""
                   Just col -> ", " <> show col) <>
                ": unexpected " <> show (L.lexemeToken lex) <>
                ", stopped at " <> show line <> ", " <> show column

lexer :: (L.Lexeme -> L.Alex a) -> L.Alex a
lexer f = (=<< skipComments) f
  where
    skipComments :: L.Alex Lexeme
    skipComments = do
      lex <- L.alexMonadScan
      res <- case lex of
               Lexeme _ (LineCommentToken _) -> skipComments
               Lexeme _ (BlockCommentToken _) -> skipComments
               _ -> return lex
      return res

parseString :: String -> Chatty.Chatty String String ParseNode
parseString programStr = case L.runAlex programStr parseQasm3 of
  Left errMsg -> Chatty.fail errMsg
  Right parseTree -> return parseTree
}
