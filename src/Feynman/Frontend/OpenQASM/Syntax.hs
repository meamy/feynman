module Feynman.Frontend.OpenQASM.Syntax where

import Feynman.Core(ID)

import Data.List

{- Abstract syntax -}
data Typ = Creg Int | Qreg Int deriving (Eq,Show)
data Arg = Var ID | Offset ID Int deriving (Eq,Show)

data UnOp  = SinOp | CosOp | TanOp | ExpOp | LnOp | SqrtOp deriving (Eq,Show)
data BinOp = PlusOp | MinusOp | TimesOp | DivOp | PowOp deriving (Eq,Show)

data QASM = QASM Double [Stmt] deriving (Eq,Show)

data Stmt =
    IncStmt String
  | DecStmt Dec
  | QStmt QExp
  | IfStmt ID Int QExp
  | BarrierStmt [Arg]
  deriving (Eq,Show)

data Dec =
    VarDec  { name :: ID,
              typ :: Typ }
  | GateDec { name :: ID,
              cparams :: [ID],
              qparams :: [ID],
              body :: [UExp] }
  | UIntDec { name :: ID,
              cparams :: [ID],
              qparams :: [ID] }
  deriving (Eq,Show)

data QExp =
    GateExp UExp
  | MeasureExp Arg Arg
  | ResetExp Arg
  deriving (Eq,Show)

data UExp =
    UGate Exp Exp Exp Arg
  | CXGate Arg Arg
  | CallGate ID [Exp] [Arg]
  deriving (Eq,Show)

data Exp =
    FloatExp Double
  | IntExp  Int
  | PiExp
  | VarExp ID
  | UOpExp UnOp Exp
  | BOpExp Exp BinOp Exp
  deriving (Eq,Show)

{- Pretty printing -}
prettyPrint :: QASM -> [String]
prettyPrint (QASM ver body) =
  ["OPENQASM " ++ show ver ++ ";"] ++ concatMap prettyPrintStmt body

prettyPrintStmt :: Stmt -> [String]
prettyPrintStmt stmt = case stmt of
  IncStmt str      -> ["include \"" ++ str ++ "\";"]
  DecStmt dec      -> prettyPrintDec dec
  QStmt qexp       -> [prettyPrintQExp qexp ++ ";"]
  IfStmt v i qexp  -> ["if(" ++ v ++ "==" ++ show i ++ ")" ++ prettyPrintQExp qexp ++ ";"]
  BarrierStmt args -> ["barrier " ++ prettyPrintArgs args ++ ";"]

prettyPrintDec :: Dec -> [String]
prettyPrintDec dec = case dec of
  VarDec x (Creg i) -> ["creg " ++ x ++ "[" ++ show i ++ "];"]
  VarDec x (Qreg i) -> ["qreg " ++ x ++ "[" ++ show i ++ "];"]
  GateDec x [] qp b ->
    ["gate " ++ x ++ " " ++ prettyPrintIDs qp, "{"]
    ++ map (\uexp -> "  " ++ prettyPrintUExp uexp ++ ";") b
    ++ ["}"]
  GateDec x cp qp b ->
    ["gate(" ++ prettyPrintIDs cp ++ ") " ++ x ++ " " ++ prettyPrintIDs qp, "{"]
    ++ map (\uexp -> "  " ++ prettyPrintUExp uexp ++ ";") b
    ++ ["}"]
  UIntDec x [] qp   ->
    ["opaque " ++ x ++ " " ++ prettyPrintIDs qp ++ ";"]
  UIntDec x cp qp   ->
    ["opaque(" ++ prettyPrintIDs cp ++ ") " ++ x ++ " " ++ prettyPrintIDs qp ++ ";"]

prettyPrintQExp :: QExp -> String
prettyPrintQExp qexp = case qexp of
  GateExp uexp         -> prettyPrintUExp uexp
  MeasureExp arg1 arg2 -> "measure " ++ prettyPrintArg arg1 ++ " -> " ++ prettyPrintArg arg2
  ResetExp arg         -> "reset " ++ prettyPrintArg arg

prettyPrintUExp :: UExp -> String
prettyPrintUExp uexp = case uexp of
  UGate e1 e2 e3 arg    ->
    "U(" ++ prettyPrintExps [e1,e2,e3] ++ ") " ++ prettyPrintArg arg
  CXGate arg1 arg2      ->
    "CX " ++ prettyPrintArgs [arg1,arg2]
  CallGate x [] qargs   ->
    x ++ " " ++ prettyPrintArgs qargs
  CallGate x exps qargs ->
    x ++ "(" ++ prettyPrintExps exps ++ ") " ++ prettyPrintArgs qargs

prettyPrintIDs :: [ID] -> String
prettyPrintIDs = intercalate ","

prettyPrintArgs :: [Arg] -> String
prettyPrintArgs = intercalate "," . map prettyPrintArg

prettyPrintArg :: Arg -> String
prettyPrintArg arg = case arg of
  Var v      -> v
  Offset v i -> v ++ "[" ++ show i ++ "]"

prettyPrintExps :: [Exp] -> String
prettyPrintExps = intercalate "," . map prettyPrintExp

prettyPrintExp :: Exp -> String
prettyPrintExp exp = case exp of
  FloatExp d           -> show d
  IntExp i             -> show i
  PiExp                -> "pi"
  VarExp v             -> v 
  UOpExp uop exp       -> prettyPrintUnOp uop ++ "(" ++ prettyPrintExp exp ++ ")"
  BOpExp exp1 bop exp2 -> prettyPrintExp exp1 ++ " " ++ prettyPrintBinOp bop ++ " " ++ prettyPrintExp exp2

prettyPrintUnOp :: UnOp -> String
prettyPrintUnOp uop = case uop of
  SinOp  -> "sin"
  CosOp  -> "cos"
  TanOp  -> "tan"
  ExpOp  -> "exp"
  LnOp   -> "ln"
  SqrtOp -> "sqrt"

prettyPrintBinOp :: BinOp -> String
prettyPrintBinOp bop = case bop of
  PlusOp  -> "+"
  MinusOp -> "-"
  TimesOp -> "*"
  DivOp   -> "/"
  PowOp   -> "^"
