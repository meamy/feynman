{
module Feynman.Frontend.OpenQASM.Lexer (Token(..), lexer) where
}

%wrapper "basic"

$digit  = 0-9        -- digits
$alpha  = [a-zA-Z]   -- alphabetic characters
$eol    = [\n]       -- newline

tokens :-

  -- Whitespace
  $white+                                                   ;
  $eol                                                      ;

  -- Comments
  \/\/.*                                                    ;

  -- Tokens 
  OPENQASM                                                  { \s -> THeader }
  include                                                   { \s -> TInclude }
  sin                                                       { \s -> TSin }
  cos                                                       { \s -> TCos }
  tan                                                       { \s -> TTan }
  exp                                                       { \s -> TExp }
  ln                                                        { \s -> TLn }
  sqrt                                                      { \s -> TSqrt }
  \+                                                        { \s -> TPlus }
  \-                                                        { \s -> TMinus }
  \*                                                        { \s -> TTimes }
  \/                                                        { \s -> TDiv }
  \^                                                        { \s -> TPow }
  pi                                                        { \s -> TPi }
  opaque                                                    { \s -> TOpaque }
  if                                                        { \s -> TIf }
  \=\=                                                      { \s -> TEq }
  barrier                                                   { \s -> TBarrier }
  gate                                                      { \s -> TGate }
  qreg                                                      { \s -> TQreg }
  creg                                                      { \s -> TCreg }
  measure                                                   { \s -> TMeasure }
  reset                                                     { \s -> TReset }
  U                                                         { \s -> TU }
  CX                                                        { \s -> TCX }
  \-\>                                                      { \s -> TArrow }
  \(                                                        { \s -> TLParen }
  \)                                                        { \s -> TRParen }
  \{                                                        { \s -> TLBrace }
  \}                                                        { \s -> TRBrace }
  \[                                                        { \s -> TLBracket }
  \]                                                        { \s -> TRBracket }
  \;                                                        { \s -> TSemicolon }
  \,                                                        { \s -> TComma }
  \"[^\"]*\"                                                { \s -> TString (filter (/='"') s) }
  [a-z]($digit|$alpha)*                                     { \s -> TID s }
  ($digit+\.$digit*|$digit*\.$digit+)([eE][\-\+]?$digit+)?  { \s -> TReal (read s) }
  [1-9]$digit*|0                                            { \s -> TNat (read s) }

{

-- OpenQASM tokens
data Token =
    THeader
  | TInclude
  -- Unary operators
  | TSin
  | TCos
  | TTan
  | TExp
  | TLn
  | TSqrt
  -- Binary operators
  | TPlus
  | TMinus
  | TTimes
  | TDiv
  | TPow
  -- Keywords
  | TPi
  | TOpaque
  | TIf
  | TEq
  | TBarrier
  | TGate
  | TQreg
  | TCreg
  | TMeasure
  | TReset
  | TU
  | TCX
  -- Symbols
  | TArrow
  | TLParen
  | TRParen
  | TLBrace
  | TRBrace
  | TLBracket
  | TRBracket
  | TSemicolon
  | TComma
  -- identifiers & literals
  | TString String
  | TID String
  | TReal Double
  | TNat Int 
  deriving (Eq,Show)

lexer :: String -> [Token]
lexer = alexScanTokens

-- vim: ft=haskell
}
