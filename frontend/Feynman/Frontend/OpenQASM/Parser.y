{
module Feynman.Frontend.OpenQASM.Parser(parse) where

import Feynman.Frontend.OpenQASM.Lexer
import Feynman.Frontend.OpenQASM.Syntax
}

%name parse
%tokentype { Token }
%error { parseError }

%token
  qasm    { THeader }
  include { TInclude }
  sin     { TSin }
  cos     { TCos }
  tan     { TTan }
  expt    { TExp }
  ln      { TLn }
  sqrt    { TSqrt }
  '+'     { TPlus }
  '-'     { TMinus }
  '*'     { TTimes }
  '/'     { TDiv }
  '^'     { TPow }
  pi      { TPi }
  opaque  { TOpaque }
  if      { TIf }
  '='     { TEq }
  barrier { TBarrier }
  gate    { TGate }
  qreg    { TQreg }
  creg    { TCreg }
  measure { TMeasure }
  '>'     { TArrow }
  reset   { TReset }
  U       { TU }
  CX      { TCX }
  '('     { TLParen }
  ')'     { TRParen }
  '{'     { TLBrace }
  '}'     { TRBrace }
  '['     { TLBracket }
  ']'     { TRBracket }
  ';'     { TSemicolon }
  ','     { TComma }
  str     { TString $$ }
  id      { TID   $$ }
  float   { TReal $$ }
  nat     { TNat  $$ }
  
%%

program : qasm float ';' statements { QASM $2 $4 }

statements : statement             { [$1] }
           | statements statement  { $1 ++ [$2] }

statement : include str ';'               { IncStmt $2 }
          | declaration                   { DecStmt $1 }
          | qop ';'                       { QStmt $1 }
          | if '(' id '=' nat ')' qop ';' { IfStmt $3 $5 $7 }

declaration : qreg id '[' nat ']' ';'                { VarDec $2 (Qreg $4) }
            | creg id '[' nat ']' ';'                { VarDec $2 (Creg $4) }
            | gate id ids '{' uops0 '}'              { GateDec $2 [] $3 $5 }
            | gate id '(' ids0 ')' ids '{' uops0 '}' { GateDec $2 $4 $6 $8 }
            | opaque id ids                          { UIntDec $2 [] $3 }
            | opaque id '(' ids0 ')' ids             { UIntDec $2 $4 $6 }

qop : uop                 { GateExp $1 }
    | measure arg '>' arg { MeasureExp $2 $4 }
    | reset arg           { ResetExp $2 }

uops0 : {- empty -} { [] }
      | uops        { $1 }

uops : uop ';'              { [$1] }
     | uops uop ';'         { $1 ++ [$2] }

uop : U '(' exp ',' exp ',' exp ')' arg { UGate $3 $5 $7 $9 }
    | CX arg ',' arg                    { CXGate $2 $4 }
    | barrier args                      { BarrierGate $2 }
    | id args                           { CallGate $1 [] $2 }
    | id '(' exps0 ')' args             { CallGate $1 $3 $5 }

args : arg          { [$1] }
     | args ',' arg { $1 ++ [$3] }

arg : id             { Var $1 }
    | id '[' nat ']' { Offset $1 $3 }

ids0 : {- empty -} { [] }
     | ids         { $1 }

ids : id         { [$1] }
    | ids ',' id { $1 ++ [$3] }

exps0 : {- empty -} { [] }
      | exps        { $1 }

exps : exp          { [$1] }
     | exps ',' exp { $1 ++ [$3] }

exp : term         { $1 }
    | exp '+' term { BOpExp $1 PlusOp $3 }
    | exp '-' term { BOpExp $1 MinusOp $3 }

term : factor          { $1 }
     | term '*' factor { BOpExp $1 TimesOp $3 }
     | term '/' factor { BOpExp $1 DivOp $3 }
     | term '^' factor { BOpExp $1 PowOp $3 }

factor : float             { FloatExp $1 }
       | nat               { IntExp $1 }
       | pi                { PiExp }
       | id                { VarExp $1 }
       | '-' factor        { BOpExp (IntExp 0) MinusOp $2 }
       | unary '(' exp ')' { UOpExp $1 $3 }
       | '(' exp ')'       { $2 }

unary : sin  { SinOp }
      | cos  { CosOp }
      | tan  { TanOp }
      | expt { ExpOp }
      | ln   { LnOp }
      | sqrt { SqrtOp }

{

parseError :: [Token] -> a
parseError xs = error $ "Parse error: " ++ concatMap show xs

-- vim: ft=haskell
}
