module Feynman.Frontend.OpenQASM.Syntax where

import Feynman.Core hiding (Stmt)
import Feynman.Frontend.DotQC (DotQC)
import qualified Feynman.Frontend.DotQC as DotQC

import Data.List

import Data.Map (Map, (!))
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
  deriving (Eq,Show)

data Dec =
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

data QExp =
    GateExp UExp
  | MeasureExp Arg Arg
  | ResetExp Arg
  deriving (Eq,Show)

data UExp =
    UGate Exp Exp Exp Arg
  | CXGate Arg Arg
  | CallGate ID [Exp] [Arg]
  | BarrierGate [Arg]
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
  BarrierGate args      ->
    "barrier " ++ prettyPrintArgs args

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
    

check :: QASM -> Either String Ctx
check (QASM _ stmts) = foldM checkStmt Map.empty stmts

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
  BarrierGate args     -> do
    let checkArg arg = do
          argTy <- argTyp ctx arg
          case argTy of
            Qreg _ -> return ()
            _      -> Left $ "Argument " ++ show arg ++ " to barrier has wrong type"
    forM_ args checkArg

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

-- Provides an optimization interface for the main IR
applyOpt :: ([Primitive] -> [Primitive]) -> QASM -> QASM
applyOpt opt (QASM ver stmts) = QASM ver $ optStmts stmts
  where optStmts stmts =
          let (hdr, body) = foldl' optStmt ([], []) stmts in
            reverse hdr ++ applyToStmts (reverse body)

        optStmt :: ([Stmt], [Stmt]) -> Stmt -> ([Stmt], [Stmt])
        optStmt (hdr, body) stmt = case stmt of
          IncStmt _                        -> (stmt:hdr, body)
          DecStmt (GateDec v c q gateBody) ->
            let stmt' = DecStmt $ GateDec v c q $ applyToUExps gateBody in
              (stmt':hdr, body)
          DecStmt _                        -> (stmt:hdr, body)
          _                                -> (hdr, stmt:body)

        applyToStmts :: [Stmt] -> [Stmt]
        applyToStmts stmts =
          let (gates, gateMap, qubitMap) = foldl' stmtToGate ([], Map.empty, Map.empty) stmts
              gates'                     = opt (reverse gates)
          in
            map (gateToStmt (gateMap, qubitMap)) gates'

        applyToUExps :: [UExp] -> [UExp]
        applyToUExps uexps =
          let (gates, gateMap, qubitMap) = foldl' uexpToGate ([], Map.empty, Map.empty) uexps
              gates'                     = opt (reverse gates)
          in
            map (gateToUExp (gateMap, qubitMap)) gates'

        stmtToGate :: ([Primitive], Map ID ([Arg] -> Stmt), Map ID Arg) -> Stmt
          -> ([Primitive], Map ID ([Arg] -> Stmt), Map ID Arg)
        stmtToGate (gates, gateMap, qubitMap) stmt = case stmt of
          IfStmt v i qexp -> -- This statement can't be desugared and hence is a nightmare
            let args      = getArgs qexp
                vars      = map prettyPrintArg args
                qubitMap' = foldr (\(x, arg) -> Map.insert x arg) qubitMap $ zip vars args
                gateName  = "If " ++ v ++ "==" ++ show i ++ " (" ++ prettyPrintQExp qexp ++ ")"
                gateMap'  = Map.insert gateName (\_ -> stmt) gateMap
            in
              ((Uninterp gateName $ v:vars):gates, gateMap', qubitMap')
          QStmt (MeasureExp arg1 arg2) ->
            let (x, y)    = (prettyPrintArg arg1, prettyPrintArg arg2)
                qubitMap' = Map.insert y arg2 $ Map.insert x arg1 qubitMap
            in
              ((Uninterp "measure" [x,y]):gates, gateMap, qubitMap')
          QStmt (ResetExp arg) ->
            let x = prettyPrintArg arg in
              ((Uninterp "reset" [x]):gates, gateMap, Map.insert x arg qubitMap)
          QStmt (GateExp uexp) ->
            let (gates', uexpGateMap, qubitMap') = uexpToGate (gates, Map.empty, qubitMap) uexp
                gateMap' = Map.union (Map.map (\f -> QStmt . GateExp . f) uexpGateMap) gateMap
            in
              (gates', gateMap', qubitMap')

        uexpToGate :: ([Primitive], Map ID ([Arg] -> UExp), Map ID Arg) -> UExp
          -> ([Primitive], Map ID ([Arg] -> UExp), Map ID Arg)
        uexpToGate (gates, gateMap, qubitMap) uexp = case uexp of
          UGate e1 e2 e3 arg ->
            let (name, x) = ("U(" ++ prettyPrintExps [e1, e2, e3] ++ ")", prettyPrintArg arg)
                gate      = Uninterp name [x]
            in
              (gate:gates, Map.insert name (UGate e1 e2 e3 . head) gateMap, Map.insert x arg qubitMap)
          CXGate arg1 arg2 ->
            let (x, y) = (prettyPrintArg arg1, prettyPrintArg arg2) in
              ((CNOT x y):gates, gateMap, Map.insert y arg2 $ Map.insert x arg1 qubitMap)
          CallGate name exps args ->
            let vars      = map prettyPrintArg args
                qubitMap' = foldr (\(x, arg) -> Map.insert x arg) qubitMap $ zip vars args
            in
              case (name, exps, vars) of
                ("h", [], x:[])       -> ((H x):gates, gateMap, qubitMap')
                ("x", [], x:[])       -> ((X x):gates, gateMap, qubitMap')
                ("y", [], x:[])       -> ((Y x):gates, gateMap, qubitMap')
                ("z", [], x:[])       -> ((Z x):gates, gateMap, qubitMap')
                ("s", [], x:[])       -> ((S x):gates, gateMap, qubitMap')
                ("sdg", [], x:[])     -> ((Sinv x):gates, gateMap, qubitMap')
                ("t", [], x:[])       -> ((T x):gates, gateMap, qubitMap')
                ("tdg", [], x:[])     -> ((Tinv x):gates, gateMap, qubitMap')
                ("cx", [], x:y:[])    -> ((CNOT x y):gates, gateMap, qubitMap')
                ("id", [], x:[])      -> (gates, gateMap, qubitMap')
                ("cz", [], x:y:[])    -> (cz x y ++ gates, gateMap, qubitMap')
                ("ccx", [], x:y:z:[]) -> (ccx x y z ++ gates, gateMap, qubitMap')
                _                     ->
                  let gateName = name ++ "(" ++ (prettyPrintExps exps) ++ ")"
                      gateMap' = Map.insert gateName (CallGate name exps) gateMap
                  in
                    ((Uninterp gateName vars):gates, gateMap', qubitMap')

        gateToStmt :: (Map ID ([Arg] -> Stmt), Map ID Arg) -> Primitive -> Stmt
        gateToStmt (gateMap, qubitMap) gate = case gate of
          H x            -> QStmt . GateExp $ CallGate "h" [] [qubitMap!x]
          X x            -> QStmt . GateExp $  CallGate "x" [] [qubitMap!x]
          Y x            -> QStmt . GateExp $  CallGate "y" [] [qubitMap!x]
          Z x            -> QStmt . GateExp $  CallGate "z" [] [qubitMap!x]
          S x            -> QStmt . GateExp $  CallGate "s" [] [qubitMap!x]
          Sinv x         -> QStmt . GateExp $  CallGate "sdg" [] [qubitMap!x]
          T x            -> QStmt . GateExp $  CallGate "t" [] [qubitMap!x]
          Tinv x         -> QStmt . GateExp $  CallGate "tdg" [] [qubitMap!x]
          CNOT x y       -> QStmt . GateExp $  CXGate (qubitMap!x) (qubitMap!y)
          Swap x y       -> QStmt . GateExp $  CallGate "swap" [] [qubitMap!x, qubitMap!y]
          Uninterp id xs -> gateMap!id $ map (qubitMap!) xs

        gateToUExp :: (Map ID ([Arg] -> UExp), Map ID Arg) -> Primitive -> UExp
        gateToUExp (gateMap, qubitMap) gate = case gate of
          H x            -> CallGate "h" [] [qubitMap!x]
          X x            -> CallGate "x" [] [qubitMap!x]
          Y x            -> CallGate "y" [] [qubitMap!x]
          Z x            -> CallGate "z" [] [qubitMap!x]
          S x            -> CallGate "s" [] [qubitMap!x]
          Sinv x         -> CallGate "sdg" [] [qubitMap!x]
          T x            -> CallGate "t" [] [qubitMap!x]
          Tinv x         -> CallGate "tdg" [] [qubitMap!x]
          CNOT x y       -> CXGate (qubitMap!x) (qubitMap!y)
          Swap x y       -> CallGate "swap" [] [qubitMap!x, qubitMap!y]
          Uninterp id xs -> gateMap!id $ map (qubitMap!) xs

        getArgs qexp = case qexp of
          MeasureExp arg1 arg2        -> [arg1, arg2]
          ResetExp arg                -> [arg]
          GateExp (UGate _ _ _ arg)   -> [arg]
          GateExp (CXGate arg1 arg2)  -> [arg1, arg2]
          GateExp (CallGate _ _ args) -> args
          
          

-- openQASM <--> .qc doesn't really make much sense. If I was smart I would have done all transformations
-- on the IR from the beginning, but this is quicker for now. Eventually I'll move everything
-- to a common IR, but for now it'll all go through .qc

-- openQASM --> .qc
{-
stmtToDotQC :: ([Gate], DotQC) -> Stmt -> ([Gate], DotQC)
stmtToDotQC (main, dotqc) stmt = case stmt of
  IncStmt s            -> (main, dotqc)
  DecStmt dec          -> (main, dotqc { decls = (decls dotqc) ++ (decToDotQC dec) })
  QStmt qexp           -> (main ++ qexpToDotQC exp, dotqc)
  IfStmt v i qexp      -> error "If statements not supported"

decToDotQC :: Dec -> Decl

toDotQC :: QASM -> DotQC
toDotQC (QASM _ stmts) = dotqc { decls = (decls dotqc) ++ [Decl "main" [] main] }
  where (main, dotqc) = foldl' stmtToDotQC ([], DotQC [] Set.empty Set.empty []) stmts
-}

-- .qc --> openQASM
regify :: ID -> Map ID Int -> ID -> Arg
regify y subs x = case Map.lookup x subs of
  Nothing -> Var x
  Just i  -> Offset y i

qcGateToQASM :: (ID -> Arg) -> DotQC.Gate -> [UExp]
qcGateToQASM sub (DotQC.Gate g i p) =
  let circ = case (g, p) of
        ("H", [x])      -> [CallGate "h" [] [sub x]]
        ("X", [x])      -> [CallGate "x" [] [sub x]]
        ("Y", [x])      -> [CallGate "y" [] [sub x]]
        ("Z", [x])      -> [CallGate "z" [] [sub x]]
        ("S", [x])      -> [CallGate "s" [] [sub x]]
        ("P", [x])      -> [CallGate "s" [] [sub x]]
        ("S*", [x])     -> [CallGate "sdg" [] [sub x]]
        ("P*", [x])     -> [CallGate "sdg" [] [sub x]]
        ("T", [x])      -> [CallGate "t" [] [sub x]]
        ("T*", [x])     -> [CallGate "tdg" [] [sub x]]
        ("tof", [x])    -> [CallGate "x" [] [sub x]]
        ("tof", [x,y])  -> [CallGate "cx" [] [sub x, sub y]]
        ("cnot", [x,y]) -> [CallGate "cx" [] [sub x, sub y]]
        ("swap", [x,y]) -> [CallGate "cx" [] [sub x, sub y],
                            CallGate "cx" [] [sub y, sub x],
                            CallGate "cx" [] [sub x, sub y]]
        ("tof", [x,y,z])-> [CallGate "ccx" [] [sub x, sub y, sub z]]
        ("Z", [x,y,z])  -> [CallGate "h" [] [sub z],
                            CallGate "ccx" [] [sub x, sub y, sub z],
                            CallGate "h" [] [sub z]]
        ("Zd", [x,y,z]) -> [CallGate "h" [] [sub z],
                            CallGate "ccx" [] [sub x, sub y, sub z],
                            CallGate "h" [] [sub z]]
        otherwise       -> [CallGate g [] (map sub p)]
  in
    concat $ genericReplicate i circ
qcGateToQASM sub (DotQC.ParamGate g i theta p) =
  let circ = case (g, p) of
        ("Rz", [x]) -> [CallGate "rz" [IntExp 0] [sub x]]
        ("Rx", [x]) -> [CallGate "rx" [IntExp 0] [sub x]]
        ("Ry", [x]) -> [CallGate "ry" [IntExp 0] [sub x]]
        otherwise   -> [CallGate g [IntExp 0] (map sub p)]
  in
    concat $ genericReplicate i circ

qcGatesToQASM :: Map ID Int -> [DotQC.Gate] -> [UExp]
qcGatesToQASM mp = concatMap (qcGateToQASM $ regify "qubits" mp)

fromDotQC :: DotQC -> QASM
fromDotQC dotqc = QASM (2.0) $ (IncStmt "qelib1.inc"):stmts
  where qMap     = Map.fromList $ zip (DotQC.qubits dotqc) [0..]
        stmts    = gateDecs ++ qDecs ++ gates
        f (DotQC.Decl name params body) = DecStmt $ GateDec name [] params (qcGatesToQASM qMap body)
        gateDecs = map f . filter ((/= "main") . DotQC.name) $ (DotQC.decls dotqc)
        qDecs    = [DecStmt $ VarDec "qubits" $ Qreg (length $ DotQC.qubits dotqc)]
        gates    = case find ((== "main") . DotQC.name) (DotQC.decls dotqc) of
          Nothing  -> []
          Just dec -> map (QStmt . GateExp) $ qcGatesToQASM qMap (DotQC.body dec)
