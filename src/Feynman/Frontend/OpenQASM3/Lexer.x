{
module Feynman.Frontend.OpenQASM3.Lexer
  (
    Alex,
    AlexPosn(..),
    Lexeme(..),
    alexError,
    alexGetInput,
    alexMonadScan,
    runAlex
  )
where

import Data.Char (chr)
import Debug.Trace (trace)
import Feynman.Frontend.OpenQASM3.Ast
import Feynman.Frontend.OpenQASM3.Syntax

}
-- This lexer was directly adapted from the official OpenQASM3 grammar from grammar/index.html

%wrapper "monad"

$nonletter              = [\@\`\!\"\#\$\%\&\'\(\)\*\+\,\-\.\/\:\;\<\=\>\?\[\\\]\^\_\{\|\}\~ $white]
$letter                 = $printable # $nonletter
-- fragment ValidUnicode: [\p{Lu}\p{Ll}\p{Lt}\p{Lm}\p{Lo}\p{Nl}]; // valid unicode chars
$firstIdCharacter       = [$letter _] -- | $validUnicode
$generalIdCharacter     = [$firstIdCharacter 0-9]
$dquote                 = \"
$squote                 = \'
$newlineSpace           = [\r\n]
$inlineSpace            = $white # $newlineSpace
$space                  = $white
$slash                  = [\/]
$star                   = [\*]

@decimalIntegerLiteral  = ([0-9] "_"?)* [0-9]

@floatLiteralExponent   = [eE] [\+\-]? @decimalIntegerLiteral

@floatLiteral           =
                        (
                          -- 1_123e-3, 123e+4 or 123E5 (needs the exponent or it's just an integer)
                          @decimalIntegerLiteral @floatLiteralExponent
                          -- .1234_5678 or .1e3 (no digits before the dot)
                          | "." @decimalIntegerLiteral @floatLiteralExponent?
                          -- 123.456, 123. or 145.32e+1_00
                          | @decimalIntegerLiteral "." @decimalIntegerLiteral? @floatLiteralExponent?
                        )


@imaginaryLiteral       = @floatLiteral $inlineSpace* "im"

@timeUnit               = "dt" | "ns" | "us" | "µs" | "ms" | "s"

OpenQASM3 :-


<0>                     ""                      { begin default_mode }

<default_mode>          "OPENQASM" / ~$generalIdCharacter
                                                { (makeLexeme OpenqasmToken) `andBegin` version_identifier }

<version_identifier>    $space+                 ;
<version_identifier>    [0-9]+ ("." [0-9]+)? / ~$generalIdCharacter
                                                { makeLexemeCat VersionSpecifierToken }
<version_identifier>    ";"                     { (makeLexeme SemicolonToken) `andBegin` default_mode }

<default_mode>          "include" / ~$generalIdCharacter
                                                { (makeLexeme IncludeToken) `andBegin` arbitrary_string }
<default_mode>          "defcalgrammar" / ~$generalIdCharacter
                                                { (makeLexeme DefcalgrammarToken) `andBegin` arbitrary_string }
<default_mode>          "cal" / ~$generalIdCharacter
                                                { (makeLexeme CalToken) `andBegin` cal_prelude }
<default_mode>          "defcal" / ~$generalIdCharacter
                                                { (makeLexeme DefcalToken) `andBegin` defcal_prelude }
<default_mode>          "#"? "pragma" / ~$generalIdCharacter
                                                { (makeLexeme PragmaToken) `andBegin` eat_to_line_end }
<default_mode>          "@" $firstIdCharacter $generalIdCharacter*
                                                { (makeLexemeCat AnnotationKeywordToken) `andBegin` eat_to_line_end }

<default_mode>          "def"                   { makeLexeme DefToken }
<default_mode>          "gate"                  { makeLexeme GateToken }
<default_mode>          "extern"                { makeLexeme ExternToken }
<default_mode>          "box"                   { makeLexeme BoxToken }
<default_mode>          "let"                   { makeLexeme LetToken }
<default_mode>          "break"                 { makeLexeme BreakToken }
<default_mode>          "continue"              { makeLexeme ContinueToken }
<default_mode>          "if"                    { makeLexeme IfToken }
<default_mode>          "else"                  { makeLexeme ElseToken }
<default_mode>          "end"                   { makeLexeme EndToken }
<default_mode>          "return"                { makeLexeme ReturnToken }
<default_mode>          "for"                   { makeLexeme ForToken }
<default_mode>          "while"                 { makeLexeme WhileToken }
<default_mode>          "in"                    { makeLexeme InToken }
<default_mode>          "input"                 { makeLexeme InputToken }
<default_mode>          "output"                { makeLexeme OutputToken }
<default_mode>          "const"                 { makeLexeme ConstToken }
<default_mode>          "readonly"              { makeLexeme ReadonlyToken }
<default_mode>          "mutable"               { makeLexeme MutableToken }
<default_mode>          "qreg"                  { makeLexeme QregToken }
<default_mode>          "qubit"                 { makeLexeme QubitToken }
<default_mode>          "creg"                  { makeLexeme CregToken }
<default_mode>          "bool"                  { makeLexeme BoolToken }
<default_mode>          "bit"                   { makeLexeme BitToken }
<default_mode>          "int"                   { makeLexeme IntToken }
<default_mode>          "uint"                  { makeLexeme UintToken }
<default_mode>          "float"                 { makeLexeme FloatToken }
<default_mode>          "angle"                 { makeLexeme AngleToken }
<default_mode>          "complex"               { makeLexeme ComplexToken }
<default_mode>          "array"                 { makeLexeme ArrayToken }
<default_mode>          "void"                  { makeLexeme VoidToken } -- unused
<default_mode>          "duration"              { makeLexeme DurationToken }
<default_mode>          "stretch"               { makeLexeme StretchToken }
<default_mode>          "gphase"                { makeLexeme GphaseToken }
<default_mode>          "inv"                   { makeLexeme InvToken }
<default_mode>          "pow"                   { makeLexeme PowToken }
<default_mode>          "ctrl"                  { makeLexeme CtrlToken }
<default_mode>          "negctrl"               { makeLexeme NegctrlToken }
<default_mode>          "#dim"                  { makeLexeme DimToken }
<default_mode>          "durationof"            { makeLexeme DurationofToken }
<default_mode>          "delay"                 { makeLexeme DelayToken }
<default_mode>          "reset"                 { makeLexeme ResetToken }
<default_mode>          "measure"               { makeLexeme MeasureToken }
<default_mode>          "barrier"               { makeLexeme BarrierToken }
<default_mode>          "true" | "false"        { makeLexemeCat BooleanLiteralToken }
<default_mode>          "["                     { makeLexeme LbracketToken }
<default_mode>          "]"                     { makeLexeme RbracketToken }
<default_mode>          "{"                     { makeLexeme LbraceToken }
<default_mode>          "}"                     { makeLexeme RbraceToken }
<default_mode>          "("                     { makeLexeme LparenToken }
<default_mode>          ")"                     { makeLexeme RparenToken }
<default_mode>          ":"                     { makeLexeme ColonToken }
<default_mode>          ";"                     { makeLexeme SemicolonToken }
<default_mode>          "."                     { makeLexeme DotToken } -- unused
<default_mode>          ","                     { makeLexeme CommaToken }
<default_mode>          "="                     { makeLexeme EqualsToken }
<default_mode>          "->"                    { makeLexeme ArrowToken }
<default_mode>          "+"                     { makeLexeme PlusToken }
<default_mode>          "++"                    { makeLexeme DoublePlusToken }
<default_mode>          "-"                     { makeLexeme MinusToken }
<default_mode>          "*"                     { makeLexeme AsteriskToken }
<default_mode>          "**"                    { makeLexeme DoubleAsteriskToken }
<default_mode>          "/"                     { makeLexeme SlashToken }
<default_mode>          "//" ~$newlineSpace*    { makeLexemeCat LineCommentToken }
<default_mode>          "/*"                    { begin block_comment }
<block_comment>         (("*" (~$slash | $newlineSpace)) | (~$star | $newlineSpace))+
                                                { makeLexemeCat BlockCommentToken }
<block_comment>         "*/"                    { begin default_mode }
<default_mode>          "%"                     { makeLexeme PercentToken }
<default_mode>          "|"                     { makeLexeme PipeToken }
<default_mode>          "||"                    { makeLexeme DoublePipeToken }
<default_mode>          "&"                     { makeLexeme AmpersandToken }
<default_mode>          "&&"                    { makeLexeme DoubleAmpersandToken }
<default_mode>          "^"                     { makeLexeme CaretToken }
<default_mode>          "@" / ~$generalIdCharacter
                                                { makeLexeme AtToken }
<default_mode>          "~"                     { makeLexeme TildeToken }
<default_mode>          "!"                     { makeLexeme ExclamationPointToken }
<default_mode>          $inlineSpace+           ; -- { makeLexemeCat WhitespaceToken }
<default_mode>          $newlineSpace+          ; -- { makeLexeme NewlineToken }
-- EqualityOperator
-- <default_mode>          "==" | "!="             { makeLexemeCat EqualityOperatorToken }
<default_mode>          "=="                    { makeLexeme DoubleEqualsToken }
<default_mode>          "!="                    { makeLexeme ExclamationPointEqualsToken }
-- CompoundAssignmentOperator
-- <default_mode>          "+=" | "-=" | "*=" | "/=" | "&=" | "|=" | "~=" | "^=" | "<<=" | ">>=" | "%=" | "**="
--                                                 { makeLexemeCat CompoundAssignmentOperatorToken }
<default_mode>          "+="                    { makeLexeme PlusEqualsToken }
<default_mode>          "-="                    { makeLexeme MinusEqualsToken }
<default_mode>          "*="                    { makeLexeme AsteriskEqualsToken }
<default_mode>          "/="                    { makeLexeme SlashEqualsToken }
<default_mode>          "&="                    { makeLexeme AmpersandEqualsToken }
<default_mode>          "|="                    { makeLexeme PipeEqualsToken }
<default_mode>          "~="                    { makeLexeme TildeEqualsToken }
<default_mode>          "^="                    { makeLexeme CaretEqualsToken }
<default_mode>          "<<="                   { makeLexeme DoubleLessEqualsToken }
<default_mode>          ">>="                   { makeLexeme DoubleGreaterEqualsToken }
<default_mode>          "%="                    { makeLexeme PercentEqualsToken }
<default_mode>          "**="                   { makeLexeme DoubleAsteriskEqualsToken }
-- ComparisonOperator
-- <default_mode>          ">" | "<" | ">=" | "<=" { makeLexemeCat ComparisonOperatorToken }
<default_mode>          "<"                     { makeLexeme LessToken }
<default_mode>          ">"                     { makeLexeme GreaterToken }
<default_mode>          "<="                    { makeLexeme LessEqualsToken }
<default_mode>          ">="                    { makeLexeme GreaterEqualsToken }
-- BitshiftOperator
<default_mode>          "<<"                    { makeLexeme DoubleLessToken }
<default_mode>          ">>"                    { makeLexeme DoubleGreaterToken }
-- <default_mode>          ">>" | "<<"             { makeLexemeCat BitshiftOperatorToken }
<default_mode>          @imaginaryLiteral / ~$generalIdCharacter
                                                { makeLexemeCat ImaginaryLiteralToken }
<default_mode>          "0" [bB] ([01] "_"?)* [01]
                                                { makeLexemeCat BinaryIntegerLiteralToken }
<default_mode>          "0o" ([0-7] "_"?)* [0-7]
                                                { makeLexemeCat OctalIntegerLiteralToken }
<default_mode>          @decimalIntegerLiteral / ~$generalIdCharacter
                                                { makeLexemeCat DecimalIntegerLiteralToken }
<default_mode>          "0" [xX] ([0-9a-fA-F] "_"?)* [0-9a-fA-F]
                                                { makeLexemeCat HexIntegerLiteralToken }
<default_mode>          $firstIdCharacter $generalIdCharacter*
                                                { makeLexemeCat IdentifierToken }
<default_mode>          "$" [0-9]+              { makeLexemeCat HardwareQubitToken }

<default_mode>          $dquote [01] ((_?) ([01]+))* $dquote
                                                { makeLexemeCat BitstringLiteralToken }

<default_mode>          @floatLiteral / ~$generalIdCharacter
                                                { makeLexemeCat FloatLiteralToken }

-- represents explicit time value in SI or backend units
<default_mode>          (@decimalIntegerLiteral | @floatLiteral) $inlineSpace* @timeUnit / ~$generalIdCharacter
                                                { makeLexemeCat TimingLiteralToken }

<arbitrary_string>      $space+                 ;
<arbitrary_string>      $dquote ($printable # $dquote)* $dquote
                                                { (makeLexemeCat StringLiteralToken) `andBegin` default_mode }
--<arbitrary_string>      $squote (~$squote)* $squote
--                                                { (makeLexemeCat StringLiteralToken) `andBegin` default_mode }

-- A different lexer mode to swap to when we need handle tokens on a line basis
-- rather than the default arbitrary-whitespace-based tokenisation.  This is
-- used by the annotation and pragma rules.
<eat_to_line_end>       $inlineSpace+           ;
<eat_to_line_end>       ~[$inlineSpace] ~[$newlineSpace]* / [$newlineSpace] -- EAT_LINE_END
                                                { makeLexemeCat RemainingLineContentToken }
<eat_to_line_end>       [$newlineSpace]         { begin default_mode }

-- We need to do a little context-aware lexing when we hit a 'cal' or 'defcal'
-- token.  In both cases, there's a small interlude before the pulse grammar
-- block starts, and we need to be able to lex our way through that.  We don't
-- want to tie this grammar to one host language by injecting host code to
-- manage the state of the lexer, so instead we need to do a little duplication
-- of the tokens, because ANTLR doesn't allow us to inherit rules directly.
<cal_prelude>           [$space]+               ; -- WHITESPACE: skip
<cal_prelude>           (LineComment | BlockComment)
                                                ; -- COMMENT: skip
<cal_prelude>           "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block }

<defcal_prelude>        [$space]+               ; -- WHITESPACE: skip
<defcal_prelude>        (LineComment | BlockComment)
                                                ; -- COMMENT: skip
<defcal_prelude>        "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block }

-- Duplications of valid constant expression tokens that may appear in the
-- argument list.  This is an unfortunately large number of duplications.

-- Types.
<defcal_prelude>        "qreg"                  { makeLexeme QregToken }
<defcal_prelude>        "qubit"                 { makeLexeme QubitToken }
<defcal_prelude>        "creg"                  { makeLexeme CregToken }
<defcal_prelude>        "bool"                  { makeLexeme BoolToken }
<defcal_prelude>        "bit"                   { makeLexeme BitToken }
<defcal_prelude>        "int"                   { makeLexeme IntToken }
<defcal_prelude>        "uint"                  { makeLexeme UintToken }
<defcal_prelude>        "angle"                 { makeLexeme AngleToken }
<defcal_prelude>        "float"                 { makeLexeme FloatToken }
<defcal_prelude>        "array"                 { makeLexeme ArrayToken }
<defcal_prelude>        "complex"               { makeLexeme ComplexToken }
<defcal_prelude>        "duration"              { makeLexeme DurationToken }
-- Punctuation.
<defcal_prelude>        "["                     { makeLexeme LbracketToken }
<defcal_prelude>        "]"                     { makeLexeme RbracketToken }
<defcal_prelude>        "("                     { makeLexeme LparenToken }
<defcal_prelude>        ")"                     { makeLexeme RparenToken }
<defcal_prelude>        "->"                    { makeLexeme ArrowToken }
<defcal_prelude>        ","                     { makeLexeme CommaToken }
<defcal_prelude>        "+"                     { makeLexeme PlusToken }
<defcal_prelude>        "-"                     { makeLexeme MinusToken }
<defcal_prelude>        "*"                     { makeLexeme AsteriskToken }
<defcal_prelude>        "/"                     { makeLexeme SlashToken }
<defcal_prelude>        "<<"                    { makeLexeme DoubleLessToken }
<defcal_prelude>        ">>"                    { makeLexeme DoubleGreaterToken }
-- Literals and names.
<defcal_prelude>        $dquote [01] ((_?) ([01]+))* $dquote
                                                { makeLexemeCat BitstringLiteralToken }
<defcal_prelude>        "0" [bB] ([01] "_"?)* [01]
                                                { makeLexemeCat BinaryIntegerLiteralToken }
<defcal_prelude>        "0o" ([0-7] "_"?)* [0-7]
                                                { makeLexemeCat OctalIntegerLiteralToken }
<defcal_prelude>        @decimalIntegerLiteral / ~$generalIdCharacter
                                                { makeLexemeCat DecimalIntegerLiteralToken }
<defcal_prelude>        "0" [xX] ([0-9a-fA-F] "_"?)* [0-9a-fA-F]
                                                { makeLexemeCat HexIntegerLiteralToken }
<defcal_prelude>        @floatLiteral / ~$generalIdCharacter
                                                { makeLexemeCat FloatLiteralToken }

<defcal_prelude>        "delay"                 { makeLexeme DelayToken }
<defcal_prelude>        "reset"                 { makeLexeme ResetToken }
<defcal_prelude>        "measure"               { makeLexeme MeasureToken }
<defcal_prelude>        $firstIdCharacter $generalIdCharacter*
                                                { makeLexemeCat IdentifierToken }
<defcal_prelude>        "$" [0-9]+              { makeLexemeCat HardwareQubitToken }

-- The meat-and-potatoes of matching a calibration block with balanced inner
-- braces.  We enter 'CAL_BLOCK' with the opening brace already tokenised
-- (that's how the lexer knew to swap modes to us), and with the token left open
-- to continue to accumulate.  We want to tokenise until we hit the balancing
-- brace.  Since we have _no_ knowledge of what the inner langauge is doing,
-- things like unbalanced braces in comments will cause a failure, but there's
-- not much we can do about that without greater spec restrictions.
<cal_block>             [~$newlineSpace $newlineSpace] # [\{\}]+
                                                { makeLexemeCat CalibrationBlockToken }
<cal_block>             "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block_2 }
<cal_block>             "}"                     { (makeLexeme RbraceToken) `andBegin` default_mode }

-- We define a max of 4 nested cal_block depths, ideally we would track the
-- nesting depth in an AlexUserState but I don't have time for that right now
<cal_block_2>           [~$newlineSpace $newlineSpace] # [\{\}]+
                                                { makeLexemeCat CalibrationBlockToken }
<cal_block_2>           "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block_3 }
<cal_block_2>           "}"                     { (makeLexeme RbraceToken) `andBegin` cal_block }

<cal_block_3>           [~$newlineSpace $newlineSpace] # [\{\}]+
                                                { makeLexemeCat CalibrationBlockToken }
<cal_block_3>           "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block_4 }
<cal_block_3>           "}"                     { (makeLexeme RbraceToken) `andBegin` cal_block_2 }

<cal_block_4>           [~$newlineSpace $newlineSpace] # [\{\}]+
                                                { makeLexemeCat CalibrationBlockToken }
<cal_block_4>           "{"                     { (makeLexeme LbraceToken) `andBegin` cal_block_4 }
<cal_block_4>           "}"                     { (makeLexeme RbraceToken) `andBegin` cal_block_3 }

{
data Lexeme = Lexeme {lexemeSource :: SourceRef, lexemeToken :: Token}
  deriving (Eq, Read, Show)

makeLexeme :: Token -> AlexInput -> Int -> Alex Lexeme
-- makeLexeme token (_, _, _, str) len | trace ("makeLexeme from \"" ++ (take len str) ++ "\"") False = undefined
makeLexeme token ((AlexPn _ l c), _, _, str) len = return (Lexeme (TextRef {sourceModule="", sourceLine=l, sourceColumn=Just c}) token)

makeLexemeCat :: (String -> Token) -> AlexInput -> Int -> Alex Lexeme
-- makeLexemeCat mkToken (_, _, _, str) len | trace ("makeLexemeCat from \"" ++ (take len str) ++ "\"") False = undefined
makeLexemeCat mkToken ((AlexPn _ l c), _, _, str) len = return (Lexeme (TextRef {sourceModule="", sourceLine=l, sourceColumn=Just c}) $ mkToken (take len str))

alexEOF = return (Lexeme NilRef EofToken)

showPosn (AlexPn _ line col) = show line ++ ':' : show col
}
