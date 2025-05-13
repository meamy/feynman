{
module Feynman.Frontend.OpenQASM3.Spec.Lexer (Token(..), lexer) where
}

%wrapper "basic"

$digit  = 0-9        -- digits
$alpha  = [a-zA-Z]   -- alphabetic characters
$eol    = [\n]       -- newline

tokens :-

  -- Whitespace
  $white+                                                   ;
  $eol                                                      ;

  -- Tokens 
  bit                                                       { \s -> TBit }
  uint                                                      { \s -> TUInt }
  pi                                                        { \s -> TPi }
  popcount                                                  { \s -> TPopcount }
  exp                                                       { \s -> TExp }
  sqrt                                                      { \s -> TSqrt }
  fun                                                       { \s -> TFun }
  sum                                                       { \s -> TSum }
  \~                                                        { \s -> TNeg }
  \!                                                        { \s -> TNeg }
  \+                                                        { \s -> TPlus }
  \-                                                        { \s -> TMinus }
  \*                                                        { \s -> TTimes }
  \/                                                        { \s -> TDiv }
  \^                                                        { \s -> TPow }
  \%                                                        { \s -> TMod }
  \<\<                                                      { \s -> TLShift }
  \<\<\<                                                    { \s -> TLRot }
  \>\>                                                      { \s -> TRShift }
  \>\>\>                                                    { \s -> TRRot }
  \-\>                                                      { \s -> TArrow }
  \-\-\>                                                    { \s -> TLongArrow }
  \(                                                        { \s -> TLParen }
  \)                                                        { \s -> TRParen }
  \{                                                        { \s -> TLBrace }
  \}                                                        { \s -> TRBrace }
  \[                                                        { \s -> TLBracket }
  \]                                                        { \s -> TRBracket }
  \:                                                        { \s -> TColon }
  \|                                                        { \s -> TBar }
  \,                                                        { \s -> TComma }
  \.                                                        { \s -> TDot }
  \`                                                        { \s -> TBacktick }
  \<                                                        { \s -> TLAngle }
  \>                                                        { \s -> TRAngle }
  \=\=                                                      { \s -> TEquals }
  \&\&                                                      { \s -> TAnd }
  [a-z]($digit|$alpha)*                                     { \s -> TID s }
  ($digit+\.$digit*|$digit*\.$digit+)([eE][\-\+]?$digit+)?  { \s -> TReal (read s) }
  [\-]*[1-9]$digit*|0                                       { \s -> TInt (read s) }

{

-- OpenQASM tokens
data Token =
    TBit
  | TUInt
  | TPi
  | TPopcount
  | TExp
  | TSqrt
  | TFun
  | TSum
  -- Unary operators
  | TNeg
  -- Binary operators
  | TPlus
  | TMinus
  | TTimes
  | TDiv
  | TPow
  | TMod
  | TLShift
  | TRShift
  | TLRot
  | TRRot
  -- Symbols
  | TArrow
  | TLongArrow
  | TLParen
  | TRParen
  | TLBrace
  | TRBrace
  | TLBracket
  | TRBracket
  | TColon
  | TBar
  | TComma
  | TDot
  | TBacktick
  | TLAngle
  | TRAngle
  | TEquals
  | TAnd
  -- identifiers & literals
  | TID String
  | TReal Double
  | TInt Int 
  deriving (Eq,Show)

lexer :: String -> [Token]
lexer = alexScanTokens

-- vim: ft=haskell
}
