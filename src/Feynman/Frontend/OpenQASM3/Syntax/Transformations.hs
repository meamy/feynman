module Feynman.Frontend.OpenQASM3.Syntax.Transformations where

import Control.Monad.State.Lazy
import Data.Char
import Data.List (intercalate, stripPrefix)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Debug.Trace (trace)
import Numeric
import Text.Read (readMaybe)

import qualified Feynman.Frontend.OpenQASM3.Ast as Ast
import Feynman.Frontend.OpenQASM3.Syntax
import Feynman.Core hiding (subst, Decl)
import Feynman.Synthesis.Phase

-- Adds unique id nuumbers to each node for identification
decorateIDs :: Ast.Node Tag c -> Ast.Node Tag Int
decorateIDs node = evalState (go node) 0 where
  go Ast.NilNode = return Ast.NilNode
  go (Ast.Node t stmts _) = do
    i <- get
    modify (+1)
    stmts' <- mapM go stmts
    return (Ast.Node t stmts' i)

data Decl c = Decl String [String] [String] (Ast.Node Tag c) deriving (Show)

getIdent :: Ast.Node Tag c -> String
getIdent (Ast.Node (Identifier name _) _ _) = name
getIdent _ = error "Not an identifier..."

getList :: Ast.Node Tag c -> [Ast.Node Tag c]
getList Ast.NilNode = []
getList (Ast.Node List stmts _) = stmts
getList _ = error "Not a list..."

asIntegerMaybe :: Ast.Node Tag c -> Maybe Integer
asIntegerMaybe node = case squashInts node of
  Ast.Node (IntegerLiteral i _) _ _ ->  Just i
  _                                 -> Nothing

asInteger :: Ast.Node Tag c -> Integer
asInteger node = case asIntegerMaybe node of
  Nothing -> trace ("Couldn't resolve integer") 0
  Just i  -> i

exprAsQlist :: Ast.Node Tag c -> [Ast.Node Tag c]
exprAsQlist node = case node of
  Ast.NilNode -> []
  (Ast.Node (Identifier name _) _ _) -> [node]
  (Ast.Node IndexedIdentifier [ident, expr] c) ->
    let idxs = resolveExpr expr in
      case idxs of
        []  -> []
        xs  -> map (\i -> Ast.Node IndexedIdentifier [ident, Ast.Node List [Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c] c] c) xs
  _       -> trace ("Couldn't resolve identifier list") []
  where
    resolveExpr Ast.NilNode = []
    resolveExpr (Ast.Node List children c) = concatMap resolveExpr children
    resolveExpr (Ast.Node (IntegerLiteral i _) _ _) = [i]
    resolveExpr (Ast.Node RangeInitExpr [b,s,e] _) =
      let bInt = asInteger b
          sInt = fromMaybe 1 $ asIntegerMaybe s
          eInt = asInteger e
      in
        [bInt,(bInt + sInt)..eInt]
    resolveExpr _ = trace ("Couldn't resolve identifier range") $ []

squashInts :: Ast.Node Tag c -> Ast.Node Tag c
squashInts Ast.NilNode = Ast.NilNode
squashInts (Ast.Node tag exprs c) =
  let exprs' = map squashInts exprs in
    case (tag, exprs') of
      (ParenExpr, [Ast.Node (IntegerLiteral i _) _ _]) -> Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c
      (UnaryOperatorExpr MinusToken, [Ast.Node (IntegerLiteral i _) _ _]) -> Ast.Node (IntegerLiteral (-i) (DecimalIntegerLiteralToken $ show (-i))) [] c
      (BinaryOperatorExpr PlusToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i+j) (DecimalIntegerLiteralToken (show $ i+j))) [] c
      (BinaryOperatorExpr MinusToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i-j) (DecimalIntegerLiteralToken (show $ i-j))) [] c
      (BinaryOperatorExpr AsteriskToken, [Ast.Node (IntegerLiteral i _) _ _, Ast.Node (IntegerLiteral j _) _ _]) -> Ast.Node (IntegerLiteral (i*j) (DecimalIntegerLiteralToken (show $ i*j))) [] c
      _ -> Ast.Node tag exprs' c

-- Applies substitutions
subst :: Map String (Ast.Node Tag c) -> Ast.Node Tag c -> Ast.Node Tag c
subst substs node = case node of
  Ast.NilNode                                                     -> Ast.NilNode
  (Ast.Node (Identifier name _) _ _) | Map.member name substs -> substs!name
  (Ast.Node tag stmts c)                                      -> Ast.Node tag (map (subst substs) stmts) c

-- Makes a basic gate call
makeBasicCall :: String -> [Ast.Node Tag c] -> c -> Ast.Node Tag c
makeBasicCall name args c =
  let target  = Ast.Node (Identifier name (IdentifierToken name)) [] c
      argList = Ast.Node List args c
  in
    Ast.Node GateCallStmt [Ast.NilNode, target, Ast.NilNode, Ast.NilNode, argList] c

-- Inlines all gate declarations
inlineGateCalls :: Ast.Node Tag c -> Ast.Node Tag c
inlineGateCalls node = squashScopes $ evalState (go node) Map.empty where
  go Ast.NilNode = return Ast.NilNode
  go node@(Ast.Node GateStmt [ident, params, args, stmts] c) = do
    stmts' <- go stmts
    modify (Map.insert (getIdent ident) $ Decl (getIdent ident) (map getIdent $ getList params) (map getIdent $ getList args) stmts')
    return node
  go node@(Ast.Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c)
    | getIdent target == "ccx" = do
        let [x,y,z] = getList gateArgs
        let gateList = [makeBasicCall "h" [z] c,
                        makeBasicCall "t" [x] c,
                        makeBasicCall "t" [y] c,
                        makeBasicCall "t" [z] c,
                        makeBasicCall "cx" [x,y] c,
                        makeBasicCall "cx" [y,z] c,
                        makeBasicCall "cx" [z,x] c,
                        makeBasicCall "tdg" [x] c,
                        makeBasicCall "tdg" [y] c,
                        makeBasicCall "t" [z] c,
                        makeBasicCall "cx" [y,x] c,
                        makeBasicCall "tdg" [x] c,
                        makeBasicCall "cx" [y,z] c,
                        makeBasicCall "cx" [z,x] c,
                        makeBasicCall "cx" [x,y] c,
                        makeBasicCall "h" [z] c]
        return $ Ast.Node Scope gateList c
    | otherwise                = do
        ctx <- get
        case Map.lookup (getIdent target) ctx of
          Nothing                          -> return node
          Just (Decl _ fparams fargs body) ->
            let substs = Map.fromList $ (zip fparams $ getList params) ++ (zip fargs $ getList gateArgs) in
              return $ subst substs body
  go (Ast.Node tag children c) = do
    children' <- mapM go children
    return $ Ast.Node tag children' c

-- Squashes extra scopes
squashScopes :: Ast.Node Tag c -> Ast.Node Tag c
squashScopes Ast.NilNode = Ast.NilNode
squashScopes (Ast.Node tag children c) =
  let children' = map squashScopes children
      squash n  = case n of
        (Ast.Node Scope xs c) -> xs
        _                     -> [n]
  in
    case tag of
      Scope -> Ast.Node tag (concatMap squash children') c
      _     -> Ast.Node tag children' c

-- Unrolls for loops
unrollLoops :: Ast.Node Tag c -> Ast.Node Tag c
unrollLoops node = squashScopes $ squashInts $ evalState (go node) Map.empty where
      -- [ScalarTypeSpec, Identifier, (Expression | Range | Set), (Statement | Scope)]
  go Ast.NilNode = return Ast.NilNode
  go node@(Ast.Node ForStmt [tyspec, ident, range, stmt] c) = do
    let var = getIdent ident
    let rn  = resolveRange range
    let ur  = map (\i -> subst (Map.fromList [(var, Ast.Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c)]) stmt) rn
    trace ("Unrolling loop over var " ++ show var ++ " with range " ++ show rn) $ return $ Ast.Node Scope ur c
  go node@(Ast.Node tag children c) = do
    children' <- mapM go children
    return $ Ast.Node tag children' c

  resolveRange Ast.NilNode = []
  resolveRange (Ast.Node RangeInitExpr [b,s,e] c) =
    let bInt = asInteger b
        sInt = fromMaybe 1 $ asIntegerMaybe s
        eInt = asInteger e
    in
      [bInt,(bInt + sInt)..eInt]

-- Builds a model of the program as a non-deterministic WHILE program
buildModel :: Ast.Node Tag Loc -> WStmt Loc
buildModel node = evalState (go node) () where
  go :: Ast.Node Tag Loc -> State () (WStmt Loc)
  go Ast.NilNode = return $ WSkip (-1)
  go (Ast.Node tag children c) = case tag of
    Program _ _ _ -> mapM go children >>= return . WSeq c
    Statement  -> go (children!!0)
    Scope      -> mapM go children >>= return . WSeq c
  -- <StatementContent>
      -- [Identifier, Expression..]
    AliasDeclStmt -> trace "Unimplemented (alias stmt)" $ return $ WSkip c
      -- [IndexedIdentifier, (Expression | MeasureExpr)]
    AssignmentStmt _ -> return $ WSkip c
      -- [(HardwareQubit | IndexedIdentifier)..]
    BarrierStmt -> trace "Unimplemented (barrier stmt)" $ return $ WSkip c
    BoxStmt    -> go (children!!1)
      -- []
    BreakStmt -> trace "Unimplemented (break stmt)" $ return $ WSkip c
      -- [ScalarTypeSpec, Identifier, DeclarationExpr]
    ConstDeclStmt -> trace "Unimplemented (const decl)" $ return $ WSkip c
      -- []
    ContinueStmt -> trace "Unimplemented (continue)" $ return $ WSkip c
      -- [Identifier, List<ArgumentDefinition>, ScalarTypeSpec?, Scope]
    DefStmt -> trace "Unimplemented (def stmt)" $ return $ WSkip c
      -- []
    EndStmt -> trace "Unimplemented (end stmt)" $ return $ WSkip c
      -- [expr]
    ExpressionStmt -> mapM go children >>= return . WSeq c
      -- [Identifier, List<ScalarTypeSpec>, returnTypeSpec::ScalarTypeSpec?]
    ExternStmt -> trace "Unimplemented (extern stmt)" $ return $ WSkip c
      -- [ScalarTypeSpec, Identifier, (Expression | Range | Set), (Statement | Scope)]
    ForStmt -> trace "Unimplemented (for stmt)" $ return $ WSkip c
      -- [Identifier, List<Identifier>?, List<Identifier>, Scope]
    GateStmt -> trace "Unimplemented (gate dec stmt)" $ return $ WSkip c
      -- [modifiers::List<GateModifier>, target::Identifier, params::List<Expression>?, designator::Expression?, args::List<(HardwareQubit | IndexedIdentifier)>?]
    GateCallStmt -> return $ case (getIdent $ children!!1) of
      "x"    -> let [x] = map pretty . getList $ children!!4 in WGate c (X x)
      "y"    -> let [x] = map pretty . getList $ children!!4 in WGate c (Y x)
      "z"    -> let [x] = map pretty . getList $ children!!4 in WGate c (Z x)
      "h"    -> let [x] = map pretty . getList $ children!!4 in WGate c (H x)
      "s"    -> let [x] = map pretty . getList $ children!!4 in WGate c (S x)
      "sdg"  -> let [x] = map pretty . getList $ children!!4 in WGate c (Sinv x)
      "t"    -> let [x] = map pretty . getList $ children!!4 in WGate c (T x)
      "tdg"  -> let [x] = map pretty . getList $ children!!4 in WGate c (Tinv x)
      "cx"   -> let [x,y] = map pretty . getList $ children!!4 in WGate c (CNOT x y)
      "cz"   -> let [x,y] = map pretty . getList $ children!!4 in WGate c (CZ x y)
      "swap" -> let [x,y] = map pretty . getList $ children!!4 in WGate c (Swap x y)
      gate   -> let xs = map pretty . getList $ children!!4 in WGate c (Uninterp gate xs)
      -- [condition::Expression, thenBlock::(Statement | Scope), elseBlock::(Statement | Scope)?
    IfStmt -> do
      thenBlock <- go (children!!1)
      elseBlock <- go (children!!2)
      return $ WIf c thenBlock elseBlock
      -- [(HardwareQubit | IndexedIdentifier), IndexedIdentifier?]
    MeasureArrowAssignmentStmt -> go (children!!0) --let x = pretty (children!!0) in return $ WMeasure c x
      -- [Identifier, designator::Expression?]
    QregOldStyleDeclStmt -> trace "Unimplemented (qreg stmt)" $ return $ WSkip c
      -- [QubitTypeSpec, Identifier]
    QuantumDeclStmt -> trace "Unimplemented (qdec stmt)" $ return $ WSkip c
      -- [(HardwareQubit | IndexedIdentifier)]
    ResetStmt -> let x = pretty (children!!0) in return $ WReset c x
      -- [(Expression | MeasureExpr)?]
    ReturnStmt -> trace "Unimplemented (return stmt)" $ return $ WSkip c
      -- [Expression, (Statement | Scope)]
    WhileStmt -> do
      block <- go (children!!1)
      return $ WWhile c block
  -- <Expression>
      -- [Expression]
    ParenExpr -> go (children!!0)
      -- [Expression, (List<RangeInitExpr | Expression> | SetInitExpr)]
    IndexExpr -> go (children!!0)
      -- [Expression]
    UnaryOperatorExpr _ -> go (children!!0)
      -- [left::Expression, right::Expression]
    BinaryOperatorExpr _ -> mapM go children >>= return . WSeq c
      -- [(ScalarTypeSpec | ArrayTypeSpec), Expression]
    CastExpr -> go (children!!1)
      -- [Scope]
    DurationOfExpr -> go (children!!0)
      -- [Identifier, List<ExpressionNode>]
    CallExpr -> trace "Unimplemented (call expr)" $ return $ WSkip c
  --   Array only allowed in array initializers
      -- [elements::Expression..]
    ArrayInitExpr -> go (children!!0)
  --   Set, Range only allowed in (some) indexing expressions
      -- [elements::Expression..]
    SetInitExpr -> go (children!!0)
      -- [begin::Expression?, step::Expression?, end::Expression?]
    RangeInitExpr -> mapM go children >>= return . WSeq c
  --   Dim only allowed in (some) array arg definitions
      -- [expr]
    MeasureExpr -> do
      let qlist = exprAsQlist (children!!0)
      return $ WSeq c $ map (WMeasure c . pretty) $ qlist
      -- [element..]
    List -> mapM go children >>= return . WSeq c
    _ -> return $ WSkip c


-- Applies a substitution list generated by phase folding
applyPFOpt :: Map Loc Angle -> Ast.Node Tag Loc -> Ast.Node Tag Loc
applyPFOpt replacements node = go node where
  go Ast.NilNode = Ast.NilNode
  go node@(Ast.Node GateCallStmt children l) = case Map.lookup l replacements of
    Nothing    -> node
    Just theta -> makeTheta theta (tail children) l
  go node@(Ast.Node tag children l) =
    let children' = map go children in
      Ast.Node tag children' l

  makeTheta theta args l =
    let prim = synthesizePhase "-" theta in
      case prim of
        [] -> Ast.NilNode
        [x] -> Ast.Node GateCallStmt ((makeIdent $ nameOfGate x):args) l

  makeIdent str = Ast.Node (Identifier str (IdentifierToken str)) [] 0

  nameOfGate gate = case gate of
    Rz theta _ -> "rz(" ++ show theta ++ ")"
    Z _        -> "z"
    S _        -> "s"
    Sinv _     -> "sdg"
    T _        -> "t"
    Tinv _     -> "tdg"

-- Applies a While statement optimization to a qasm 3 program
applyWStmtOpt :: ([ID] -> [ID] -> WStmt Loc -> Map Loc Angle) -> Ast.Node Tag Loc -> Ast.Node Tag Loc
applyWStmtOpt opt node = applyPFOpt (opt vlst vlst wstmt) node' where
  node' = decorateIDs node -- recompute to make sure IDs are unique
  wstmt = buildModel node'
  vlst  = idsW wstmt

-- Counts gate calls
countGateCalls :: Ast.Node Tag c -> Map String Int
countGateCalls node = go Map.empty node where
  go counts Ast.NilNode = counts
  go counts node@(Ast.Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c) =
    let id = getIdent target in
      Map.insertWith (+) id 1 counts
  go counts (Ast.Node tag children c) = foldl go counts children

-- Print out
showStats :: Ast.Node Tag c -> [String]
showStats = (map f . Map.toList) . countGateCalls where
  f (gate, count) = gate ++ ": " ++ show count
