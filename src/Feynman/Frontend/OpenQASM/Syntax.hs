module Feynman.Frontend.OpenQASM.Syntax where

import Feynman.Core(ID)

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

data Exp =
    FloatExp Double
  | IntExp  Int
  | PiExp
  | VarExp ID
  | UOpExp UnOp Exp
  | BOpExp Exp BinOp Exp
  deriving (Eq,Show)

data Dec =
    GateDec { name :: ID,
              cparams :: [ID],
              qparams :: [ID],
              body :: [UExp] }
  | UIntDec { name :: ID,
              cparams :: [ID],
              qparams :: [ID] }
  | VarDec  { name :: ID,
              typ :: Typ }
  deriving (Eq,Show)

data UExp =
    UGate Exp Exp Exp Arg
  | CXGate Arg Arg
  | CallGate ID [Exp] [Arg]
  deriving (Eq,Show)

data QExp =
    GateExp UExp
  | MeasureExp Arg Arg
  | ResetExp Arg
  deriving (Eq,Show)


{- Pretty printing -}
--prettyPrint :: QASM -> [String]
