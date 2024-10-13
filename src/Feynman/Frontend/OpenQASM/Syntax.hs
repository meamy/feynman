{-# LANGUAGE DeriveGeneric #-} 
module Feynman.Frontend.OpenQASM.Syntax where

import Feynman.Core hiding (Stmt)
import Feynman.Frontend.DotQC (DotQC)
import qualified Feynman.Frontend.DotQC as DotQC

import Data.List
import Data.Char (isDigit, isAlpha)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Control.Monad
import Debug.Trace

{- Abstract syntax -}
data Typ = Numeric | Creg Int | Qreg Int | Circ Int Int deriving (Eq,Show,Generic)
data Arg = Var ID | Offset ID Int deriving (Eq,Show,Generic)

data UnOp  = SinOp | CosOp | TanOp | ExpOp | LnOp | SqrtOp deriving (Eq,Show,Generic)
data BinOp = PlusOp | MinusOp | TimesOp | DivOp | PowOp deriving (Eq,Show,Generic)

data QASM = QASM Double [Stmt] deriving (Eq,Show,Generic)

data Stmt =
    IncStmt String
  | DecStmt Dec
  | QStmt QExp
  | IfStmt ID Int QExp
  deriving (Eq,Show,Generic)

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
  deriving (Eq,Show,Generic)

data QExp =
    GateExp UExp
  | MeasureExp Arg Arg
  | ResetExp Arg
  deriving (Eq,Show,Generic)

data UExp =
    UGate Exp Exp Exp Arg
  | CXGate Arg Arg
  | CallGate ID [Exp] [Arg]
  | BarrierGate [Arg]
  deriving (Eq,Show,Generic)

data Exp =
    FloatExp Double
  | IntExp  Int
  | PiExp
  | VarExp ID
  | UOpExp UnOp Exp
  | BOpExp Exp BinOp Exp
  deriving (Eq,Show,Generic)

instance NFData Typ
instance NFData Arg
instance NFData UnOp
instance NFData BinOp
instance NFData QASM
instance NFData Stmt
instance NFData Dec
instance NFData QExp
instance NFData UExp
instance NFData Exp

{- Expression evaluation -}
evalUOp :: UnOp -> (Double -> Double)
evalUOp op = case op of
  SinOp  -> sin
  CosOp  -> cos
  TanOp  -> tan
  ExpOp  -> exp
  LnOp   -> log
  SqrtOp -> sqrt

evalBOp :: BinOp -> (Double -> Double -> Double)
evalBOp op = case op of
  PlusOp  -> (+)
  MinusOp -> (-)
  TimesOp -> (*)
  DivOp   -> (/)
  PowOp   -> (**)

evalExp :: Exp -> Maybe Double
evalExp exp = case exp of
  FloatExp f          -> Just $ f
  IntExp i            -> Just $ fromIntegral i
  PiExp               -> Just $ pi
  VarExp _            -> Nothing
  UOpExp op exp       -> liftM (evalUOp op) $ evalExp exp
  BOpExp exp1 op exp2 -> do
    e1 <- evalExp exp1
    e2 <- evalExp exp2
    return $ (evalBOp op) e1 e2
  
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
    ["gate " ++ x ++ " " ++ prettyPrintIDs qp ++ " {"]
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

substUExp esub asub uexp = case uexp of
  UGate e1 e2 e3 a -> UGate (substExp esub e1)
                            (substExp esub e2)
                            (substExp esub e3)
                            (substArg asub a)
  CXGate a b       -> CXGate (substArg asub a) (substArg asub b)
  BarrierGate xs   -> BarrierGate (map (substArg asub) xs)
  CallGate v e xs  -> CallGate v (map (substExp esub) e) (map (substArg asub) xs)

substExp esub exp = case exp of
  VarExp v         -> Map.findWithDefault (VarExp v) v esub
  UOpExp uop exp   -> UOpExp uop (substExp esub exp)
  BOpExp e1 bop e2 -> BOpExp (substExp esub e1) bop (substExp esub e2)
  _                -> exp

substArg asub arg = case arg of
  Var v  -> Map.findWithDefault (Var v) v asub
  _      -> arg

-- Expands all implicitly mapped functions
desugar :: Ctx -> QASM -> QASM
desugar symtab (QASM ver stmts) = QASM ver $ concatMap f stmts
  where f stmt = case stmt of
          IncStmt _       -> [stmt]
          -- By the specification of QASM, functions can only refer to
          -- parameters in their body, which are explicitly qubit typed
          DecStmt _       -> [stmt]
          QStmt qexp      -> map QStmt $ g qexp
          -- Note that we can't expand v due to the design of QASM. Fun.
          IfStmt v i qexp -> map (IfStmt v i) $ g qexp
        g qexp = case qexp of
          MeasureExp a b  -> zipWith MeasureExp (expand a) (expand b)
          ResetExp a      -> map ResetExp $ expand a
          GateExp uexp    -> map GateExp $ h uexp
        h uexp = case uexp of
          UGate e1 e2 e3 a -> map (UGate e1 e2 e3) $ expand a
          CXGate a b       -> zipWith CXGate (expand a) (expand b)
          BarrierGate xs   -> [BarrierGate $ concatMap expand xs]
          -- Can cause problems if not all argument registers have the same length
          CallGate v e xs  -> map (CallGate v e) $ transpose (map expand xs)
        expand arg = case arg of
          Offset _ _ -> [arg]
          Var v      -> case symtab!v of
            Qreg i -> map (Offset v) [0..i-1]
            Creg i -> map (Offset v) [0..i-1]
            _      -> [Var v]

-- Inlines all local definitions & non-primitive operations
-- Note: non-strictness can hopefully allow for some efficient
--       fusion with operations on inlined code
inline :: QASM -> QASM
inline (QASM ver stmts) = QASM ver . snd . foldl f (Map.empty, []) $ stmts
  where f (ctx, stmts) stmt = case stmt of
          DecStmt (GateDec v c q b) -> (Map.insert v (c, q, concatMap (h ctx) b) ctx, stmts)
          QStmt qexp                -> (ctx, stmts ++ (map QStmt $ g ctx qexp))
          IfStmt v i qexp           -> (ctx, stmts ++ (map (IfStmt v i) $ g ctx qexp))
          _                         -> (ctx, stmts ++ [stmt])
        g ctx qexp = case qexp of
          GateExp uexp    -> map GateExp $ h ctx uexp
          _               -> [qexp]
        h ctx uexp = case uexp of
          CallGate v e xs -> inlineCall ctx v e xs
          _               -> [uexp]
        inlineCall ctx v e xs = case Map.lookup v ctx of
          Just (c, q, b)  ->
            let eSubs = Map.fromList $ zip c e
                aSubs = Map.fromList $ zip q xs
            in
              map (substUExp eSubs aSubs) b
          Nothing         -> [CallGate v e xs]

-- Provides an optimization interface for the main IR
applyOpt :: ([ID] -> [ID] -> [Primitive] -> [Primitive]) -> Bool -> QASM -> QASM
applyOpt opt pureCircuit (QASM ver stmts) = QASM ver $ optStmts stmts
  where optStmts stmts =
          let (hdr, body) = foldl' optStmt ([], []) stmts in
            reverse hdr ++ applyToStmts (reverse body)

        optStmt :: ([Stmt], [Stmt]) -> Stmt -> ([Stmt], [Stmt])
        optStmt (hdr, body) stmt = case stmt of
          IncStmt _                        -> (stmt:hdr, body)
          DecStmt (GateDec _ _ _ [])       -> (stmt:hdr, body)
          DecStmt (GateDec v c q gateBody) ->
            let stmt' = DecStmt $ GateDec v c q $ applyToUExps q gateBody in
              (stmt':hdr, body)
          DecStmt _                        -> (stmt:hdr, body)
          _                                -> (hdr, stmt:body)

        applyToStmts :: [Stmt] -> [Stmt]
        applyToStmts stmts =
          let (gates, gateMap, qubitMap) = foldl' stmtToGate ([], Map.empty, Map.empty) stmts
              vars                       = ids gates
              inputs                     = if pureCircuit then vars else []
              gates'                     = opt vars inputs (reverse gates)
          in
            map (gateToStmt (gateMap, qubitMap)) gates'

        applyToUExps :: [ID] -> [UExp] -> [UExp]
        applyToUExps inp uexps =
          let (gates, gateMap, qubitMap) = foldl' uexpToGate ([], Map.empty, Map.empty) uexps
              vars                       = ids gates
              inputs                     = if pureCircuit then vars else inp
              gates'                     = opt vars inputs (reverse gates)
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
          BarrierGate args ->
            let vars      = map prettyPrintArg args
                qubitMap' = foldr (\(x, arg) -> Map.insert x arg) qubitMap $ zip vars args
            in
              ((Uninterp "barrier" vars):gates, gateMap, qubitMap')
          CallGate name exps args ->
            let vars      = map prettyPrintArg args
                qubitMap' = foldr (\(x, arg) -> Map.insert x arg) qubitMap $ zip vars args
            in
              case (name, exps, vars) of
                ("h", [], x:[])             -> ((H x):gates, gateMap, qubitMap')
                ("x", [], x:[])             -> ((X x):gates, gateMap, qubitMap')
                ("y", [], x:[])             -> ((Y x):gates, gateMap, qubitMap')
                ("z", [], x:[])             -> ((Z x):gates, gateMap, qubitMap')
                ("s", [], x:[])             -> ((S x):gates, gateMap, qubitMap')
                ("sdg", [], x:[])           -> ((Sinv x):gates, gateMap, qubitMap')
                ("t", [], x:[])             -> ((T x):gates, gateMap, qubitMap')
                ("tdg", [], x:[])           -> ((Tinv x):gates, gateMap, qubitMap')
                ("cx", [], x:y:[])          -> ((CNOT x y):gates, gateMap, qubitMap')
                ("id", [], x:[])            -> (gates, gateMap, qubitMap')
                ("cz", [], x:y:[])          -> ((CZ x y):gates, gateMap, qubitMap')
                ("ccx", [], x:y:z:[])       -> (ccx x y z ++ gates, gateMap, qubitMap')
                ("rz", [theta], x:[])
                  | Just a <- evalExp theta -> ((Rz (Continuous a) x):gates, gateMap, qubitMap')
                _                           ->
                  let gateName = name ++ "(" ++ (prettyPrintExps exps) ++ ")"
                      gateMap' = Map.insert gateName (CallGate name exps) gateMap
                  in
                    ((Uninterp gateName vars):gates, gateMap', qubitMap')

        gateToStmt :: (Map ID ([Arg] -> Stmt), Map ID Arg) -> Primitive -> Stmt
        gateToStmt (gateMap, qubitMap) gate = case gate of
          H x                      -> QStmt . GateExp $ CallGate "h" [] [qubitMap!x]
          X x                      -> QStmt . GateExp $ CallGate "x" [] [qubitMap!x]
          Y x                      -> QStmt . GateExp $ CallGate "y" [] [qubitMap!x]
          Z x                      -> QStmt . GateExp $ CallGate "z" [] [qubitMap!x]
          S x                      -> QStmt . GateExp $ CallGate "s" [] [qubitMap!x]
          Sinv x                   -> QStmt . GateExp $ CallGate "sdg" [] [qubitMap!x]
          T x                      -> QStmt . GateExp $ CallGate "t" [] [qubitMap!x]
          Tinv x                   -> QStmt . GateExp $ CallGate "tdg" [] [qubitMap!x]
          CNOT x y                 -> QStmt . GateExp $ CXGate (qubitMap!x) (qubitMap!y)
          CZ x y                   -> QStmt . GateExp $ CallGate "cz" [] [qubitMap!x, qubitMap!y]
          Swap x y                 -> QStmt . GateExp $ CallGate "swap" [] [qubitMap!x, qubitMap!y]
          Rz (Continuous t) x      -> QStmt . GateExp $ CallGate "rz" [FloatExp t] [qubitMap!x]
          Uninterp "measure" [x,y] -> QStmt $ MeasureExp (qubitMap!x) (qubitMap!y)
          Uninterp "reset" [x]     -> QStmt $ ResetExp (qubitMap!x)
          Uninterp "barrier" xs    -> QStmt $ GateExp $ BarrierGate $ map (qubitMap!) xs
          Uninterp id xs           -> gateMap!id $ map (qubitMap!) xs

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
          CZ x y         -> CallGate "cz" [] [qubitMap!x, qubitMap!y]
          Swap x y       -> CallGate "swap" [] [qubitMap!x, qubitMap!y]
          Uninterp "barrier" xs -> BarrierGate $ map (qubitMap!) xs
          Uninterp id xs        -> gateMap!id $ map (qubitMap!) xs

        getArgs qexp = case qexp of
          MeasureExp arg1 arg2        -> [arg1, arg2]
          ResetExp arg                -> [arg]
          GateExp (UGate _ _ _ arg)   -> [arg]
          GateExp (CXGate arg1 arg2)  -> [arg1, arg2]
          GateExp (CallGate _ _ args) -> args
          GateExp (BarrierGate args)  -> args
          
{- Statistics -}

-- Assumes inlined code
gateCounts :: QASM -> Map ID Int
gateCounts (QASM ver stmts) = foldl gcStmt Map.empty stmts
  where gcStmt cnts stmt = case stmt of
          IncStmt _       -> cnts
          DecStmt _       -> cnts 
          QStmt qexp      -> gcQExp cnts qexp
          IfStmt _ _ qexp -> gcQExp cnts qexp
        gcQExp cnts qexp = case qexp of
          GateExp uexp         -> gcUExp cnts uexp
          MeasureExp arg1 arg2 -> addToCount 1 "measurement" cnts
          ResetExp arg1        -> addToCount 1 "reset" cnts
        gcUExp cnts uexp = case uexp of
          UGate e1 e2 e3 _     ->
            let name = "U(" ++ prettyPrintExps [e1, e2, e3] ++ ")" in
              addToCount 1 name cnts
          CXGate _ _           -> addToCount 1 "cnot" cnts
          CallGate name exps _ -> case name of
            "h"   -> addToCount 1 "H" cnts
            "x"   -> addToCount 1 "X" cnts
            "y"   -> addToCount 1 "Y" cnts
            "z"   -> addToCount 1 "Z" cnts
            "s"   -> addToCount 1 "S" cnts
            "sdg" -> addToCount 1 "S" cnts
            "t"   -> addToCount 1 "T" cnts
            "tdg" -> addToCount 1 "T" cnts
            "cx"  -> addToCount 1 "cnot" cnts
            "id"  -> cnts
            "cz"  -> addToCount 1 "cz" cnts
            "ccx" -> addToCount 2 "H" $ addToCount 7 "cnot" $ addToCount 7 "T" cnts
            _     -> addToCount 1 (name ++ "(" ++ (prettyPrintExps exps) ++ ")") cnts
          BarrierGate _     -> cnts

        addToCount i str cnts =
          let alterf val = case val of
                Nothing -> Just i
                Just c  -> Just $ c+i
          in
            Map.alter alterf str cnts

bitCounts :: QASM -> (Int, Int)
bitCounts (QASM ver stmts) = foldl bcStmt (0, 0) stmts
  where bcStmt cnts stmt = case stmt of
          DecStmt dec  -> bcDec cnts dec
          _            -> cnts
        bcDec (cbits, qbits) dec = case dec of
          VarDec _ (Creg i) -> (cbits + i, qbits)
          VarDec _ (Qreg i) -> (cbits, qbits + i)
          _                 -> (cbits, qbits)

{- Cross compilation -}

-- .qc --> openQASM
regify :: ID -> Map ID Int -> ID -> Arg
regify y subs x = case Map.lookup x subs of
  Nothing -> Var x
  Just i  -> Offset y i

isValidIDChar :: Char -> Bool
isValidIDChar c = isAlpha c || isDigit c || c == '_'

validate :: ID -> ID
validate [] = []
validate (x:xs)
  | isAlpha x = foldr go [] (x:xs)
  | otherwise = "q" ++ foldr go [] (x:xs)
  where go x acc | isValidIDChar x = x:acc
                 | otherwise       = acc

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

fromDotQC :: String -> DotQC -> QASM
fromDotQC mainName dotqc = QASM (2.0) $ (IncStmt "qelib1.inc"):stmts where
  stmts = map go $ DotQC.decls dotqc
  go (DotQC.Decl name loc body)
    | name == "main" = DecStmt $ GateDec (validate mainName) [] (glob ++ map validate loc) (convert body)
    | otherwise      = DecStmt $ GateDec (validate name) [] (glob ++ map validate loc) (convert body)
  glob = map validate $ DotQC.qubits dotqc
  convert = concatMap (qcGateToQASM $ Var . validate)
