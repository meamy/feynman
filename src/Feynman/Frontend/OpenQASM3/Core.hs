{-|
Module      : Core
Description : Core openQASM 3 abstract syntax
Copyright   : (c) Matthew Amy, 2025
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
-}

module Feynman.Frontend.OpenQASM3.Core where

import Control.Monad
import Data.Complex
import Data.Bits

import Feynman.Core (ID)
import qualified Feynman.Frontend.OpenQASM3.Syntax as S

{- Translation errors -}
data ErrMsg = Err String

{- Convenience types -}
type Annotation = String
type Version    = (Int, Maybe Int)

{- Core AST -}
data Type a = TCBit       -- Symbolic
            | TCReg (Expr a)  -- Symbolic
            | TQBit       -- Symbolic
            | TQReg (Expr a)  -- Symbolic
            | TUInt (Expr a)  -- Symbolic
            | TAngle
            | TBool
            | TInt
            | TFloat
            | TCmplx
            | TProc [Type a]
            deriving (Show)

data AccessPath a = AVar ID
                  | AIndex ID (Expr a)
                  deriving (Show)

data Modifier a = MCtrl Bool (Maybe (Expr a))
                | MInv
                | MPow (Expr a)
                deriving (Show)

data Expr a = EVar ID
            | EIndex (Expr a) (Expr a)
            | ECall [Modifier a] ID [(Expr a)]
            | EMeasure (Expr a)
            | EInt Int
            | EFloat Double
            | ECmplx (Complex Double)
            | ESlice (Expr a) (Maybe (Expr a)) (Expr a) -- Inclusive on both ends
            | ESet [(Expr a)]
            | EPi
            | EIm
            | EBool Bool
            | EUOp UOp (Expr a)
            | EBOp (Expr a) BinOp (Expr a)
            | EStmt (Stmt a)
            deriving (Show)

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
         deriving (Show)

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
           | GTOp -- >
           | GEqOp -- >=
           | PlusOp -- +
           | MinusOp -- -
           | TimesOp -- *
           | DivOp -- / 
           | ModOp -- %
           | PowOp -- **
           | ConcatOp -- ++, not used in openQASM 3 spec
           deriving (Show)

data Decl a =
    DVar { vid :: ID, typ :: Type a, val :: Maybe (Expr a) }
  | DDef { did :: ID, dparams :: [(ID, Type a)], dreturns :: Maybe (Type a), dbody :: Stmt a }
  | DExtern { eid :: ID, eparams :: [(Type a)], ereturns :: Maybe (Type a) }
  | DAlias { aid :: ID, aexps :: [(Expr a)] }
  deriving (Show)

data Stmt a =
    SInclude a String
  | SSkip a
  | SDeclare a (Decl a)
  | SBarrier a [AccessPath a]
  | SBlock a [Stmt a]
  | SExpr a (Expr a)
  | SAssign a (AccessPath a) (Maybe BinOp) (Expr a)
  | SFor a (ID, Type a) (Expr a) (Stmt a)
  | SIf a (Expr a) (Stmt a) (Stmt a)
  | SReset a (Expr a)
  | SReturn a (Expr a)
  | SWhile a (Expr a) (Stmt a)
  | SAnnotated a [Annotation] (Stmt a)
  | SPragma a String
  deriving (Show)

-- Top level core QASM3 programs
data Prog a = Prog Version [Stmt a] deriving (Show)

{- Utilities -}

-- | Gets the identifier being declared
declID :: Decl a -> ID
declID decl = case decl of
  (DVar id _ _) -> id
  (DDef id _ _ _) -> id
  (DExtern id _ _) -> id
  (DAlias id _) -> id

-- | Applies a monadic computation to a list of nodes
inLst :: (S.ParseNode -> Either ErrMsg b) -> S.ParseNode -> Either ErrMsg [b]
inLst f S.NilNode            = return []
inLst f (S.Node S.List xs c) = mapM f xs
inLst f node                 = Left (Err $ "Malformed list: " ++ show node)

{- Translation passes -}

-- | Translation from concrete syntax to the core subset
qasmToCore :: S.ParseNode -> Either ErrMsg (Prog S.SourceRef)
qasmToCore = translateProg

-- | Top-level translation
translateProg :: S.ParseNode -> Either ErrMsg (Prog S.SourceRef)
translateProg node = case node of
  S.Node (S.Program i j _) xs _ -> mapM translateStmt xs >>= return . Prog (i,j)
  _                             -> Left (Err $ "Malformed Program: " ++ show node)

-- | Type translations
translateType :: S.ParseNode -> Either ErrMsg (Type S.SourceRef)
translateType node = case node of
  S.Node S.BitTypeSpec [S.NilNode] c -> return $ TCBit
  S.Node S.BitTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TCReg

  S.Node S.IntTypeSpec _ c -> return $ TInt

  S.Node S.UintTypeSpec [S.NilNode] c -> return $ TUInt (EInt 32)
  S.Node S.UintTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TUInt

  S.Node S.FloatTypeSpec _ c -> return $ TFloat

  S.Node S.AngleTypeSpec _ c -> return $ TAngle

  S.Node S.BoolTypeSpec _ c -> return $ TBool

  S.Node S.DurationTypeSpec _ c -> return $ TFloat

  S.Node S.StretchTypeSpec _ c -> return $ TFloat

  S.Node S.ComplexTypeSpec _ c -> return $ TCmplx

  S.Node S.CregTypeSpec [S.NilNode] c -> return $ TCBit
  S.Node S.CregTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TCReg

  S.Node S.QregTypeSpec [S.NilNode] c -> return $ TQBit
  S.Node S.QregTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TQReg

  S.Node S.QubitTypeSpec [S.NilNode] c -> return $ TQBit
  S.Node S.QubitTypeSpec [exprnode] c -> translateExpr exprnode >>= return . TQReg

  S.Node S.ArrayTypeSpec _ c ->
    Left (Err "Array types unsupported")

  S.Node S.ReadonlyArrayRefTypeSpec _ c ->
    Left (Err "Array types unsupported")

  S.Node S.MutableArrayRefTypeSpec _ c ->
    Left (Err "Array types unsupported")

-- | Identifier translations
translateIdent :: S.ParseNode -> Either ErrMsg ID
translateIdent node = case node of
  S.Node (S.Identifier id _) [] c -> return id
  _                          -> Left (Err $ "Malformed identifier: " ++ show node)

-- | Access path translations
translateAccessPath :: S.ParseNode -> Either ErrMsg (AccessPath S.SourceRef)
translateAccessPath node = case node of
  S.Node (S.HardwareQubit idx _) [] c -> return $ AVar ("$" ++ show idx)

  S.Node S.IndexedIdentifier [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ AIndex id idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  S.Node S.IndexExpr [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ AIndex id idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  _                          -> Left (Err $ "Malformed access path: " ++ show node)

-- | Translation of Expressions
translateExpr :: S.ParseNode -> Either ErrMsg (Expr S.SourceRef)
translateExpr node = case node of
  S.Node S.ParenExpr [exprnode] c -> translateExpr exprnode

  S.Node S.IndexExpr [exprnode, idxnode] c -> do
    expr <- translateExpr exprnode
    idxs  <- inLst translateExpr idxnode
    case idxs of
      [idx] -> return $ EIndex expr idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  S.Node (S.UnaryOperatorExpr uop) [exprnode] c -> do
    op   <- translateUOp uop
    expr <- translateExpr exprnode
    return $ EUOp op expr

  S.Node (S.BinaryOperatorExpr bop) [leftnode, rightnode] c -> do
    op    <- translateBOp bop
    left  <- translateExpr leftnode
    right <- translateExpr rightnode
    return $ EBOp left op right

  S.Node S.CastExpr [exprnode] c -> translateExpr exprnode

  S.Node S.DurationOfExpr [stmtnode] c -> do
    stmt <- translateStmt stmtnode
    return $ EStmt stmt

  S.Node S.CallExpr [idnode, exprnodes] c -> do
    id    <- translateIdent idnode
    exprs <- inLst translateExpr exprnodes
    return $ ECall [] id exprs

  S.Node S.ArrayInitExpr _ c ->
    Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Arrays unsupported")

  S.Node S.SetInitExpr exprs c -> do
    mapM translateExpr exprs >>= return . ESet

  S.Node S.RangeInitExpr [beginnode, stepnode, endnode] c -> do
    begin <- translateExpr beginnode
    step <- (case stepnode of S.NilNode -> return Nothing; node -> liftM Just $ translateExpr stepnode)
    end <- translateExpr endnode
    return $ ESlice begin step end

  S.Node S.DimExpr [expr] c -> 
    Left (Err "Array types unsupported")

  S.Node S.MeasureExpr [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ EMeasure expr

  S.Node (S.Identifier id _) [] c -> return $ EVar id

  S.Node (S.IntegerLiteral i _) [] c -> return $ EInt (fromInteger i)

  S.Node (S.FloatLiteral r _) [] c -> return $ EFloat r

  S.Node (S.ImaginaryLiteral r _) [] c -> return $ ECmplx (0 :+ r)

  S.Node (S.BooleanLiteral b _) [] c -> return $ EBool b

  S.Node (S.BitstringLiteral xs _) [] c -> return $ EInt (intOfBitstring xs)

  S.Node (S.TimingLiteral _ _) [] c -> return $ EInt 0

  S.Node (S.HardwareQubit i _) [] c -> return $ EVar ("#" ++ show i)

  S.Node S.IndexedIdentifier [idnode, idxlist] c -> do
    id   <- translateIdent idnode
    idxs <- inLst translateExpr idxlist
    case idxs of
      [idx] -> return $ EIndex (EVar id) idx
      _     -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Multiple indices unsupported")

  _                          -> Left (Err $ "Malformed expression: " ++ show node)

  where intOfBitstring xs =
          foldr (+) 0 . map (\(b,i) -> if b then shift 1 i else 0) $ zip xs [0..]

-- | Translation of gate modifiers
translateModifier :: S.ParseNode -> Either ErrMsg (Modifier S.SourceRef)
translateModifier node = case node of
  S.Node S.PowGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MPow expr

  S.Node S.InvGateModifier [] c -> return $ MInv

  S.Node S.CtrlGateModifier [S.NilNode] c -> return $ MCtrl False Nothing
  S.Node S.CtrlGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MCtrl False (Just expr)

  S.Node S.NegCtrlGateModifier [S.NilNode] c -> return $ MCtrl True Nothing
  S.Node S.NegCtrlGateModifier [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ MCtrl True (Just expr)

  _                          -> Left (Err $ "Malformed modifier: " ++ show node)

-- | Translation of Annotations
translateAnnotation :: S.ParseNode -> Either ErrMsg Annotation
translateAnnotation node = case node of
  S.Node (S.Annotation _ str _) [] c -> return str
  _                                  -> Left (Err $ "Malformed annotation: " ++ show node)

-- | Translation of Arguments
translateArg :: S.ParseNode -> Either ErrMsg (ID, Type S.SourceRef)
translateArg node = case node of
  S.Node S.ArgumentDefinition [typespec, idnode] c -> do
    typ <- translateType typespec
    id <- translateIdent idnode
    return $ (id, typ)

  _                                  -> Left (Err $ "Malformed argument: " ++ show node)

-- | Translation of statements
translateStmt :: S.ParseNode -> Either ErrMsg (Stmt S.SourceRef)
translateStmt node = case node of
  S.NilNode -> return $ SSkip S.NilRef
  
  S.Node (S.Pragma str _) [] c -> return $ SPragma c str

  S.Node S.Statement [stmt] c -> translateStmt stmt

  S.Node S.Statement (stmt:xs) c -> do
    annots <- mapM translateAnnotation xs
    s <- translateStmt stmt
    return $ SAnnotated c annots s

  S.Node S.Scope stmts c -> do
    mapM translateStmt stmts >>= return . SBlock c

  S.Node S.AliasDeclStmt (idnode:exprnodes) c -> do
    id <- translateIdent idnode
    exprs <- mapM translateExpr exprnodes
    return $ SDeclare c (DAlias id exprs)

  S.Node (S.AssignmentStmt op) [idnode, exprnode] c -> do
    idexpr <- translateAccessPath idnode
    expr <- translateExpr exprnode
    assop <- translateCompoundAOp op
    return $ SAssign c idexpr assop expr

  S.Node (S.BarrierStmt) idnodes c -> do
    idexprs <- mapM translateAccessPath idnodes
    return $ SBarrier c idexprs

  S.Node S.BoxStmt [_, scope@(S.Node S.Scope _ _)] _ -> translateStmt scope

  S.Node S.BreakStmt [] c -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Break unsupported")

  S.Node (S.CalStmt _) [] c -> return $ SSkip c
  S.Node (S.DefcalgrammarStmt _ _) [] c -> return $ SSkip c

  S.Node S.ClassicalDeclStmt [typespec, idnode, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent idnode
    expr <- (case initexpr of S.NilNode -> return Nothing; node -> liftM Just $ translateExpr node)
    return $ SDeclare c (DVar id ty expr)

  S.Node S.ConstDeclStmt [typespec, idnode, initexpr] c -> do
    ty <- translateType typespec
    id <- translateIdent idnode
    expr <- translateExpr initexpr
    return $ SDeclare c (DVar id ty (Just expr))

  S.Node S.ContinueStmt [] c   ->
    Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Continue unsupported")

  S.Node S.DefStmt [idnode, argnodes, rettype, stmt] c -> do
    id <- translateIdent idnode
    args <- inLst translateArg argnodes
    ret <- (case rettype of S.NilNode -> return Nothing; node -> liftM Just $ translateType node)
    body <- translateStmt stmt
    return $ SDeclare c (DDef id args ret body)

  S.Node S.DefcalStmt _ c -> return $ SSkip c

  S.Node S.DelayStmt _ c -> return $ SSkip c

  S.Node S.EndStmt [] c -> Left (Err $ "Error at " ++ (S.pp_source c) ++ ": End unsupported")

  S.Node S.ExpressionStmt [exprnode] c -> 
    translateExpr exprnode >>= return . SExpr c

  S.Node S.ExternStmt [idnode, typenodes, rettype] c -> do
    id <- translateIdent idnode
    types <- inLst translateType typenodes
    ret <- (case rettype of S.NilNode -> return Nothing; node -> liftM Just $ translateType node)
    return $ SDeclare c (DExtern id types ret)

  S.Node S.ForStmt [typenode, idnode, exprnode, stmtnode] c -> do
    typ <- translateType typenode
    id <- translateIdent idnode
    expr <- translateExpr exprnode
    body <- translateStmt stmtnode
    return $ SFor c (id, typ) expr body

  S.Node S.GateStmt [idnode, cargnodes, qargnodes, stmt] c -> do
    id <- translateIdent idnode
    cargs <- (case cargnodes of S.NilNode -> return []; node -> inLst translateIdent node)
    qargs <- inLst translateIdent qargnodes
    body <- translateStmt stmt
    let args = zip cargs (repeat TCmplx) ++ zip qargs (repeat TQBit)
    return $ SDeclare c (DDef id args Nothing body)

  S.Node S.GateCallStmt [modnodes, idnode, paramnodes, _, argnodes] c -> do
    modifiers <- inLst translateModifier modnodes
    id <- translateIdent idnode
    params <- inLst translateExpr paramnodes
    args <- inLst translateExpr argnodes
    return $ SExpr c (ECall modifiers id (params ++ args))
    
  S.Node S.IfStmt [condnode, thennode, elsenode] c -> do
    cond <- translateExpr condnode
    thn <- translateStmt thennode
    els <- translateStmt elsenode
    return $ SIf c cond thn els

  S.Node (S.IncludeStmt path _) [] c -> return $ SSkip c
    --Left (Err $ "Error at " ++ (S.pp_source c) ++ ": include unsupported")

  S.Node S.InputIoDeclStmt [typenode, idnode] c -> do
    ty <- translateType typenode
    id <- translateIdent idnode
    return $ SDeclare c (DVar id ty Nothing)

  S.Node S.OutputIoDeclStmt [typenode, idnode] c -> do
    ty <- translateType typenode
    id <- translateIdent idnode
    return $ SDeclare c (DVar id ty Nothing)

  S.Node S.MeasureArrowAssignmentStmt [srcidexpr, tgtidexpr] c -> do
    srcid <- translateAccessPath srcidexpr
    tgtid <- translateExpr tgtidexpr
    return $ SAssign c srcid Nothing (EMeasure tgtid)

  S.Node S.CregOldStyleDeclStmt [idnode, exprnode] c -> do
    id <- translateIdent idnode
    case exprnode of
      S.NilNode -> return $ SDeclare c (DVar id TCBit Nothing)
      node      -> do
        expr <- translateExpr node
        return $ SDeclare c (DVar id (TCReg expr) Nothing)

  S.Node S.QregOldStyleDeclStmt [idnode, exprnode] c -> do
    id <- translateIdent idnode
    case exprnode of
      S.NilNode -> return $ SDeclare c (DVar id TQBit Nothing)
      node -> do
        expr <- translateExpr node
        return $ SDeclare c (DVar id (TQReg expr) Nothing)

  S.Node S.QuantumDeclStmt [typenode, idnode] c -> do
    id <- translateIdent idnode
    typ <- translateType typenode
    return $ SDeclare c (DVar id typ Nothing)

  S.Node (S.ResetStmt) [exprnode] c -> do
    expr <- translateExpr exprnode
    return $ SReset c expr

  S.Node S.ReturnStmt [] c   ->
    Left (Err $ "Error at " ++ (S.pp_source c) ++ ": Return unsupported")

  S.Node S.WhileStmt [condnode, bodynode] c -> do
    cond <- translateExpr condnode
    body <- translateStmt bodynode
    return $ SWhile c cond body

  _                           -> Left (Err $ "Malformed statement: " ++ show node)

-- | Translation of unary operators
translateUOp :: S.Token -> Either ErrMsg UOp
translateUOp token = case token of
  S.MinusToken                -> return UMinusOp
  S.TildeToken                -> return NegOp
  S.ExclamationPointToken     -> return NegOp

-- | Translation of binary operators
translateBOp :: S.Token -> Either ErrMsg BinOp
translateBOp token = case token of
  S.PlusToken            -> return PlusOp
  S.DoublePlusToken      -> return ConcatOp
  S.MinusToken           -> return MinusOp
  S.AsteriskToken        -> return TimesOp
  S.DoubleAsteriskToken  -> return PowOp
  S.SlashToken           -> return DivOp
  S.PercentToken         -> return ModOp
  S.PipeToken            -> return OrOp
  S.DoublePipeToken      -> return OrOp
  S.AmpersandToken       -> return AndOp
  S.DoubleAmpersandToken -> return AndOp
  S.CaretToken           -> return XorOp
  S.LessToken            -> return LTOp
  S.LessEqualsToken      -> return LEqOp
  S.GreaterToken         -> return GTOp
  S.GreaterEqualsToken   -> return GEqOp
  S.DoubleLessToken      -> return LShiftOp
  S.DoubleGreaterToken   -> return RShiftOp
  S.DoubleEqualsToken    -> return EqOp

-- | Translation of compound assignment operators
translateCompoundAOp :: S.Token -> Either ErrMsg (Maybe BinOp)
translateCompoundAOp token = case token of
  S.EqualsToken               -> return Nothing
  S.PlusEqualsToken           -> return $ Just PlusOp
  S.MinusEqualsToken          -> return $ Just MinusOp
  S.AsteriskEqualsToken       -> return $ Just TimesOp
  S.SlashEqualsToken          -> return $ Just DivOp
  S.AmpersandEqualsToken      -> return $ Just AndOp
  S.PipeEqualsToken           -> return $ Just OrOp
  S.CaretEqualsToken          -> return $ Just XorOp
  S.DoubleLessEqualsToken     -> return $ Just LShiftOp
  S.DoubleGreaterEqualsToken  -> return $ Just RShiftOp
  S.PercentEqualsToken        -> return $ Just ModOp
  S.DoubleAsteriskEqualsToken -> return $ Just PowOp
