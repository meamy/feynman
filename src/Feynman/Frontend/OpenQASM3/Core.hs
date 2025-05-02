{-|
Module      : CoreQASM
Description : Core openQASM 3 abstract syntax
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3

data Type = CRegTy Int   -- Symbolic
          | QRegTy Int   -- Symbolic
          | UIntTy Int   -- Symbolic
          | AngleTy Int  -- Symbolic
          | BoolTy       -- Symbolic
          | IntTy
          | FloatTy
          | CmplxTy
          | ProcTy [Typ]
          deriving (Eq,Show)

data Expr = VarExpr ID
          | IndexExpr Expr [Expr]
          | SliceExpr Expr (Maybe Expr) Expr -- Inclusive on both ends
          | CallExpr Expr [Expr]
          | MeasurExpr Expr
          | IntExpr Int
          | FloatExpr Double
          | PiExpr
          | ImExpr
          | BoolExpr Bool
          | UOpExp UOp Exp
          | BOpExp Exp BinOp Exp
          | CtrlExp [Expr] Expr
          | InvExp Expr
          deriving (Eq,Show)

data UOp = SinOp
         | CosOp
         | TanOp
         | ArccosOp
         | ArcsinOp
         | ArctanOp
         | CeilOp
         | FloorOp
         | ExpOp
         | LnOp
         | SqrtOp
         | RealOp
         | ImOp
         | NegOp -- ~, !
         | UMinusOp -- -
         | PopcountOp -- popcount
         deriving (Eq,Show)

data BinOp = AndOp -- &, &&
           | OrOp  -- |, ||
           | XorOp -- ^
           | LShiftOp  -- <<
           | RShiftOp -- >>
           | LRotOp  -- rotl
           | RRotOp -- rotr
           | EqOp -- ==
           | LTOp -- <
           | LEqOp -- <=
           | RTOp -- >
           | REqOp -- >=
           | PlusOp -- +
           | MinusOp -- -
           | TimesOp -- *
           | DivOp -- / 
           | ModOp -- %
           | PowOp -- **
           deriving (Eq,Show)

data Stmt =
    IncludeStmt String
  | DeclareStmt Decl
  | BarrierStmt [Expr]
  | AssignmentStmt { lval :: Expr, rval :: Expr }
  | DefStmt { name :: ID, params :: [(ID, Type)], returns :: (Maybe Type), defbody :: [Stmt] }
  | ForStmt { idx :: (ID, Type), range :: Expr, forbody :: [Stmt] }
  | IfStmt { ifcond :: Expr, thenbranch :: [Stmt], :: elsebranch [Stmt] }
  | ResetStmt Expr
  | ReturnStmt Expr
  | WhileStmt { whilecond :: Expr, whilebodyd :: [Stmt] }
  | AnnotatedStmt { annot :: String, stmt :: Stmt }
  deriving (Eq,Show)

data Decl =
    VarDec  { id :: ID,
              typ :: Typ }
  | GateDec { id :: ID,
              cparams :: [ID],
              qparams :: [ID],
              gates :: [UExp] }
  | UIntDec { id :: ID,
              cparams :: [ID],
              qparams :: [ID] }
  deriving (Eq,Show)
