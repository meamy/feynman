{
module Feynman.Frontend.OpenQASM.Lexer (Token(..), lexer) where

import Data.Maybe
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
  \/\/\:.*                                                  { \s -> TMacro s }
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
  sum                                                       { \s -> TSum }
  qubit                                                     { \s -> TQubitType }
  int                                                       { \s -> TIntType }
  ancilla                                                   { \s -> TAncillaType }
  \-\>                                                      { \s -> TArrow }
  \(                                                        { \s -> TLParen }
  \)                                                        { \s -> TRParen }
  \{                                                        { \s -> TLBrace }
  \}                                                        { \s -> TRBrace }
  \[                                                        { \s -> TLBracket }
  \]                                                        { \s -> TRBracket }
  \:                                                        { \s -> TColon }
  \;                                                        { \s -> TSemicolon }
  \,                                                        { \s -> TComma }
  \|                                                        { \s -> TBar }
  \<                                                        { \s -> TLangle }
  \>                                                        { \s -> TRangle }
  \-\-\>                                                    { \s -> TMapsto }
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
  | TColon
  | TSemicolon
  | TComma
  -- identifiers & literals
  | TString String
  | TID String
  | TReal Double
  | TNat Int 
  -- Specifications
  | TMacro String
  | TAnnot
  | TBar
  | TLangle
  | TRangle
  | TMapsto
  | TSum
  -- Types for specifications
  | TQubitType
  | TIntType
  | TAncillaType
  deriving (Eq,Show)

lexer :: String -> [Token]
lexer = concatMap go . alexScanTokens where
  go (TMacro str) = (TAnnot:(alexScanTokens $ drop 3 str))
  go tok          = [tok]

-- vim: ft=haskell
}
