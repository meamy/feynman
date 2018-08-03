module Feynman.Frontend.OpenQASM.Syntax where

import Feynman.Core(ID)

import Data.List

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Debug.Trace

{- Abstract syntax -}
data Typ = Numeric | Creg Int | Qreg Int | Circ Int Int deriving (Eq,Show)
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
emit :: QASM -> IO ()
emit = mapM_ putStrLn . prettyPrint

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

{- Semantic analysis -}

type Ctx = Map ID Typ

-- Hard coded qelib, easier for now
qelib1 :: Ctx
qelib1 = Map.fromList
  [ ("u3", Circ 3 1),
    ("u2", Circ 2 1),
    ("u1", Circ 1 1),
    ("cx", Circ 0 2),
    ("id", Circ 0 1),
    ("x", Circ 0 1),
    ("y", Circ 0 1),
    ("z", Circ 0 1),
    ("h", Circ 0 1),
    ("s", Circ 0 1),
    ("sdg", Circ 0 1),
    ("t", Circ 0 1),
    ("tdg", Circ 0 1),
    ("rx", Circ 1 1),
    ("ry", Circ 1 1),
    ("rz", Circ 1 1),
    ("cz", Circ 0 2),
    ("cy", Circ 0 2),
    ("ch", Circ 0 2),
    ("ccx", Circ 0 3),
    ("crz", Circ 1 2),
    ("cu1", Circ 1 2),
    ("cu3", Circ 3 2) ]
    

check :: QASM -> Either String ()
check (QASM _ stmts) = foldM_ checkStmt Map.empty stmts

checkStmt :: Ctx -> Stmt -> Either String Ctx
checkStmt ctx stmt = case stmt of
  IncStmt "qelib1.inc" -> return $ Map.union qelib1 ctx
  IncStmt s            -> return ctx
  DecStmt dec          -> checkDec ctx dec
  QStmt qexp           -> do
    checkQExp ctx qexp
    return ctx
  IfStmt v i qexp      -> do
    vTy <- argTyp ctx (Var v)
    case vTy of
      Creg _ -> return ()
      _      -> Left $ "Variable " ++ v ++ " in if statement has wrong type"
    checkQExp ctx qexp
    return ctx
  BarrierStmt args     -> do
    let checkArg arg = do
          argTy <- argTyp ctx arg
          case argTy of
            Qreg _ -> return ()
            _      -> Left $ "Argument " ++ show arg ++ " to barrier has wrong type"
    forM_ args checkArg
    return ctx

-- Note that we don't require that arguments in the body of a dec are not offsets
checkDec :: Ctx -> Dec -> Either String Ctx
checkDec ctx dec = case dec of
  VarDec v typ      -> return $ Map.insert v typ ctx
  UIntDec v cp qp   -> return $ Map.insert v (Circ (length cp) (length qp)) ctx
  GateDec v cp qp b -> do
    let ctx' = foldr (\v -> Map.insert v (Qreg 1)) (foldr (\v -> Map.insert v Numeric) ctx cp) qp
    forM_ b (checkUExp ctx')
    return $ Map.insert v (Circ (length cp) (length qp)) ctx

checkQExp :: Ctx -> QExp -> Either String ()
checkQExp ctx qexp = case qexp of
  GateExp uexp         -> checkUExp ctx uexp
  MeasureExp arg1 arg2 -> do
    arg1Ty <- argTyp ctx arg1
    arg2Ty <- argTyp ctx arg2
    case (arg1Ty, arg2Ty) of
      (Qreg i, Creg j) ->
        if i == j
        then return ()
        else Left $ "Registers " ++ show arg1 ++ ", " ++ show arg2 ++ " have different size"
      _                ->
        Left $ "Arguments " ++ show arg1 ++ ", " ++ show arg2 ++ " have wrong types"
  ResetExp arg         -> do
    argTy <- argTyp ctx arg
    case argTy of
      Qreg _ -> return ()
      _      -> Left $ "Argument " ++ show arg ++ " to reset has wrong type"

checkUExp :: Ctx -> UExp -> Either String ()
checkUExp ctx uexp = case uexp of
  UGate theta phi lambda arg -> do
    forM_ [theta, phi, lambda] (checkExp ctx)
    argTy <- argTyp ctx arg
    case argTy of
      Qreg i -> return ()
      _      -> Left $ "Argument " ++ show arg ++ " to U gate has wrong type"
  CXGate arg1 arg2           -> do
    arg1Ty <- argTyp ctx arg1
    arg2Ty <- argTyp ctx arg2
    case (arg1Ty, arg2Ty) of
      (Qreg i, Qreg j) ->
        if i == j
        then return ()
        else Left $ "Registers " ++ show arg1 ++ ", " ++ show arg2 ++ " have different size"
      _                ->
        Left $ "Arguments " ++ show arg1 ++ ", " ++ show arg2 ++ " have wrong types"
  CallGate v exps args       -> do
    let checkArg arg = do
          argTy <- argTyp ctx arg
          case argTy of
            Qreg _ -> return ()
            _      -> Left $ "Argument " ++ show arg ++ " to " ++ v ++ " has wrong type"
    vTy <- argTyp ctx (Var v)
    forM_ exps (checkExp ctx)
    forM_ args checkArg
    case vTy of
      Circ i j ->
        if i == length exps && j == length args
        then return ()
        else Left $ "Wrong number of arguments to " ++ v
      _ -> Left $ "Variable " ++ v ++ " is not gate type"

checkExp :: Ctx -> Exp -> Either String ()
checkExp ctx exp = case exp of
  VarExp v           -> do
    vTy <- argTyp ctx (Var v)
    case vTy of
      Numeric -> return ()
      _       -> Left $ "Variable " ++ v ++ " has wrong type in expression"
  UOpExp _ exp       -> checkExp ctx exp
  BOpExp exp1 _ exp2 -> checkExp ctx exp1 >> checkExp ctx exp2
  _                  -> return ()

argTyp :: Ctx -> Arg -> Either String Typ
argTyp ctx (Var v) = case Map.lookup v ctx of
  Nothing -> Left $ "No binding for " ++ v
  Just ty -> return ty
argTyp ctx (Offset v i) = do
  baseTy <- argTyp ctx (Var v)
  case baseTy of
    Qreg j ->
      if i >= 0 && i < j
      then return $ Qreg 1
      else Left $ "Index " ++ show i ++ " out of bounds"
    Creg j ->
      if i >= 0 && i < j
      then return $ Creg 1
      else Left $ "Index " ++ show i ++ " out of bounds"
    _      -> Left $ "Variable " ++ v ++ " invalid for offset"
     

{- Transformations -}
-- Doing double duty wrt .qc frontend. If I was smart I would have done all transformations
-- on the IR from the beginning, but this is quicker for now. Eventually I'll move everything
-- to a common IR.

--inlineQASM :: QASM -> QASM
