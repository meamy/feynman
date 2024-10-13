module Feynman.Frontend.OpenQASM3.Syntax.Transformations where

import Control.Monad.State.Lazy
import Data.Char
import Data.List (intercalate, stripPrefix)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Feynman.Algebra.Base (DyadicRational (..), unpack)
import Feynman.Core (Angle (..), ID, Loc, Primitive (..), WStmt (..), idsW, simplifyWStmt')
import Feynman.Frontend.OpenQASM3.Ast
import Feynman.Frontend.OpenQASM3.Semantics
import Feynman.Frontend.OpenQASM3.Syntax
import Feynman.Synthesis.Phase
import Numeric
import Text.Read (readMaybe)

-- For disabling tracing until these transformations
-- can be integrating with a logging monad
trace :: String -> a -> a
trace _ a = a

-- Adds unique id numbers to each node for identification
decorateIDs :: Node Tag c -> Node Tag Int
decorateIDs node = evalState (go node) 0
  where
    go NilNode = return NilNode
    go (Node t stmts _) = do
      i <- get
      modify (+ 1)
      stmts' <- mapM go stmts
      return (Node t stmts' i)

data Decl c = Decl String [String] [String] (Node Tag c) deriving (Show)

getIdent :: Node Tag c -> String
getIdent (Node (Identifier name _) _ _) = name
getIdent _ = error "Not an identifier..."

getList :: Node Tag c -> [Node Tag c]
getList NilNode = []
getList (Node List stmts _) = stmts
getList _ = error "Not a list..."

asIntegerMaybe :: Node Tag c -> Maybe Integer
asIntegerMaybe node = case squashInts node of
  Node (IntegerLiteral i _) _ _ -> Just i
  _ -> Nothing

asInteger :: Node Tag c -> Integer
asInteger node = case asIntegerMaybe node of
  Nothing -> trace ("Couldn't resolve integer") 0
  Just i -> i

exprFromAngle :: Angle -> SyntaxNode ()
exprFromAngle (Discrete dy)
  | a == 0 = integerLiteralNode 0
  | a == 1 = identifierNode "pi"
  | otherwise =
      binOpNode
        AsteriskToken
        (identifierNode "pi")
        $ binOpNode
          SlashToken
          (integerLiteralNode a)
          (binOpNode DoubleAsteriskToken (integerLiteralNode 2) (integerLiteralNode $ fromIntegral n))
  where
    (Dy a n) = unpack dy
exprFromAngle (Continuous a) = floatLiteralNode a

exprAsQlist :: Node Tag c -> [Node Tag c]
exprAsQlist node = case node of
  NilNode -> []
  (Node (Identifier name _) _ _) -> [node]
  (Node IndexedIdentifier [ident, expr] c) ->
    let idxs = resolveExpr expr
     in case idxs of
          [] -> []
          xs -> map (\i -> Node IndexedIdentifier [ident, Node List [Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c] c] c) xs
  _ -> trace ("Couldn't resolve identifier list") []
  where
    resolveExpr NilNode = []
    resolveExpr (Node List children c) = concatMap resolveExpr children
    resolveExpr (Node (IntegerLiteral i _) _ _) = [i]
    resolveExpr (Node RangeInitExpr [b, s, e] _) =
      let bInt = asInteger b
          sInt = fromMaybe 1 $ asIntegerMaybe s
          eInt = asInteger e
       in [bInt, (bInt + sInt) .. eInt]
    resolveExpr _ = trace ("Couldn't resolve identifier range") $ []

squashInts :: Node Tag c -> Node Tag c
squashInts NilNode = NilNode
squashInts (Node tag exprs c) =
  let exprs' = map squashInts exprs
   in case (tag, exprs') of
        (ParenExpr, [Node (IntegerLiteral i _) _ _]) -> Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c
        (UnaryOperatorExpr MinusToken, [Node (IntegerLiteral i _) _ _]) -> Node (IntegerLiteral (-i) (DecimalIntegerLiteralToken $ show (-i))) [] c
        (BinaryOperatorExpr PlusToken, [Node (IntegerLiteral i _) _ _, Node (IntegerLiteral j _) _ _]) -> Node (IntegerLiteral (i + j) (DecimalIntegerLiteralToken (show $ i + j))) [] c
        (BinaryOperatorExpr MinusToken, [Node (IntegerLiteral i _) _ _, Node (IntegerLiteral j _) _ _]) -> Node (IntegerLiteral (i - j) (DecimalIntegerLiteralToken (show $ i - j))) [] c
        (BinaryOperatorExpr AsteriskToken, [Node (IntegerLiteral i _) _ _, Node (IntegerLiteral j _) _ _]) -> Node (IntegerLiteral (i * j) (DecimalIntegerLiteralToken (show $ i * j))) [] c
        _ -> Node tag exprs' c

-- Applies substitutions
subst :: Map String (Node Tag c) -> Node Tag c -> Node Tag c
subst substs node = case node of
  NilNode -> NilNode
  (Node (Identifier name _) _ _) | Map.member name substs -> substs ! name
  (Node tag stmts c) -> Node tag (map (subst substs) stmts) c

-- Makes a basic gate call
makeBasicCall :: String -> [Node Tag c] -> c -> Node Tag c
makeBasicCall name args c =
  let target = Node (Identifier name (IdentifierToken name)) [] c
      argList = Node List args c
   in Node GateCallStmt [NilNode, target, NilNode, NilNode, argList] c

-- Inlines all gate declarations
inlineGateCalls :: Node Tag c -> Node Tag c
inlineGateCalls node = squashScopes $ evalState (go node) Map.empty
  where
    go NilNode = return NilNode
    go node@(Node GateStmt [ident, params, args, stmts] c) = do
      stmts' <- go stmts
      modify (Map.insert (getIdent ident) $ Decl (getIdent ident) (map getIdent $ getList params) (map getIdent $ getList args) stmts')
      return NilNode
    go node@(Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c)
      | getIdent target == "ccx" = do
          let [x, y, z] = getList gateArgs
          let gateList =
                [ makeBasicCall "h" [z] c,
                  makeBasicCall "t" [x] c,
                  makeBasicCall "t" [y] c,
                  makeBasicCall "t" [z] c,
                  makeBasicCall "cx" [x, y] c,
                  makeBasicCall "cx" [y, z] c,
                  makeBasicCall "cx" [z, x] c,
                  makeBasicCall "tdg" [x] c,
                  makeBasicCall "tdg" [y] c,
                  makeBasicCall "t" [z] c,
                  makeBasicCall "cx" [y, x] c,
                  makeBasicCall "tdg" [x] c,
                  makeBasicCall "cx" [y, z] c,
                  makeBasicCall "cx" [z, x] c,
                  makeBasicCall "cx" [x, y] c,
                  makeBasicCall "h" [z] c
                ]
          return $ Node Scope gateList c
      | otherwise = do
          ctx <- get
          case Map.lookup (getIdent target) ctx of
            Nothing -> return node
            Just (Decl _ fparams fargs body) ->
              let substs = Map.fromList $ (zip fparams $ getList params) ++ (zip fargs $ getList gateArgs)
               in return $ subst substs body
    go (Node tag children c) = do
      children' <- mapM go children
      return $ Node tag children' c

-- Squashes extra scopes
squashScopes :: Node Tag c -> Node Tag c
squashScopes NilNode = NilNode
squashScopes (Node tag children c) =
  let children' = map squashScopes children
      squash n = case n of
        (Node Scope xs c) -> xs
        _ -> [n]
   in case tag of
        Scope -> Node tag (concatMap squash children') c
        _ -> Node tag children' c

-- Unrolls for loops
unrollLoops :: Node Tag c -> Node Tag c
unrollLoops node = squashScopes $ squashInts $ evalState (go node) Map.empty
  where
    -- [ScalarTypeSpec, Identifier, (Expression | Range | Set), (Statement | Scope)]
    go NilNode = return NilNode
    go node@(Node ForStmt [tyspec, ident, range, stmt] c) = do
      let var = getIdent ident
      let rn = resolveRange range
      let ur = map (\i -> subst (Map.fromList [(var, Node (IntegerLiteral i (DecimalIntegerLiteralToken $ show i)) [] c)]) stmt) rn
      trace ("Unrolling loop over var " ++ show var ++ " with range " ++ show rn) $ return $ Node Scope ur c
    go node@(Node tag children c) = do
      children' <- mapM go children
      return $ Node tag children' c

    resolveRange NilNode = []
    resolveRange (Node RangeInitExpr [b, s, e] c) =
      let bInt = asInteger b
          sInt = fromMaybe 1 $ asIntegerMaybe s
          eInt = asInteger e
       in [bInt, (bInt + sInt) .. eInt]

-- Builds a model of the program as a non-deterministic WHILE program
buildModel :: Node Tag Loc -> WStmt Loc
buildModel node = evalState (go node) ()
  where
    go :: Node Tag Loc -> State () (WStmt Loc)
    go NilNode = return $ WSkip (-1)
    go (Node tag children c) = case tag of
      Program _ _ _ -> mapM go children >>= return . WSeq c
      Statement -> go (children !! 0)
      Scope -> mapM go children >>= return . WSeq c
      -- <StatementContent>
      -- [Identifier, Expression..]
      AliasDeclStmt -> trace "Unimplemented (alias stmt)" $ return $ WSkip c
      -- [IndexedIdentifier, (Expression | MeasureExpr)]
      AssignmentStmt _ -> return $ WSkip c
      -- [(HardwareQubit | IndexedIdentifier)..]
      BarrierStmt -> trace "Unimplemented (barrier stmt)" $ return $ WSkip c
      BoxStmt -> go (children !! 1)
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
      GateCallStmt -> return $ case (getIdent $ children !! 1) of
        "x" -> let [x] = map pretty . getList $ children !! 4 in WGate c (X x)
        "y" -> let [x] = map pretty . getList $ children !! 4 in WGate c (Y x)
        "z" -> let [x] = map pretty . getList $ children !! 4 in WGate c (Z x)
        "h" -> let [x] = map pretty . getList $ children !! 4 in WGate c (H x)
        "s" -> let [x] = map pretty . getList $ children !! 4 in WGate c (S x)
        "sdg" -> let [x] = map pretty . getList $ children !! 4 in WGate c (Sinv x)
        "t" -> let [x] = map pretty . getList $ children !! 4 in WGate c (T x)
        "tdg" -> let [x] = map pretty . getList $ children !! 4 in WGate c (Tinv x)
        "cx" -> let [x, y] = map pretty . getList $ children !! 4 in WGate c (CNOT x y)
        "cz" -> let [x, y] = map pretty . getList $ children !! 4 in WGate c (CZ x y)
        "swap" -> let [x, y] = map pretty . getList $ children !! 4 in WGate c (Swap x y)
        gate -> let xs = map pretty . getList $ children !! 4 in WGate c (Uninterp gate xs)
      -- [condition::Expression, thenBlock::(Statement | Scope), elseBlock::(Statement | Scope)?
      IfStmt -> do
        thenBlock <- go (children !! 1)
        elseBlock <- go (children !! 2)
        return $ WIf c thenBlock elseBlock
      -- [(HardwareQubit | IndexedIdentifier), IndexedIdentifier?]
      MeasureArrowAssignmentStmt -> go (children !! 0) -- let x = pretty (children!!0) in return $ WMeasure c x
      -- [Identifier, designator::Expression?]
      QregOldStyleDeclStmt -> trace "Unimplemented (qreg stmt)" $ return $ WSkip c
      -- [QubitTypeSpec, Identifier]
      QuantumDeclStmt -> trace "Unimplemented (qdec stmt)" $ return $ WSkip c
      -- [(HardwareQubit | IndexedIdentifier)]
      ResetStmt -> let x = pretty (children !! 0) in return $ WReset c x
      -- [(Expression | MeasureExpr)?]
      ReturnStmt -> trace "Unimplemented (return stmt)" $ return $ WSkip c
      -- [Expression, (Statement | Scope)]
      WhileStmt -> do
        block <- go (children !! 1)
        return $ WWhile c block
      -- <Expression>
      -- [Expression]
      ParenExpr -> go (children !! 0)
      -- [Expression, (List<RangeInitExpr | Expression> | SetInitExpr)]
      IndexExpr -> go (children !! 0)
      -- [Expression]
      UnaryOperatorExpr _ -> go (children !! 0)
      -- [left::Expression, right::Expression]
      BinaryOperatorExpr _ -> mapM go children >>= return . WSeq c
      -- [(ScalarTypeSpec | ArrayTypeSpec), Expression]
      CastExpr -> go (children !! 1)
      -- [Scope]
      DurationOfExpr -> go (children !! 0)
      -- [Identifier, List<ExpressionNode>]
      CallExpr -> trace "Unimplemented (call expr)" $ return $ WSkip c
      --   Array only allowed in array initializers
      -- [elements::Expression..]
      ArrayInitExpr -> go (children !! 0)
      --   Set, Range only allowed in (some) indexing expressions
      -- [elements::Expression..]
      SetInitExpr -> go (children !! 0)
      -- [begin::Expression?, step::Expression?, end::Expression?]
      RangeInitExpr -> mapM go children >>= return . WSeq c
      --   Dim only allowed in (some) array arg definitions
      -- [expr]
      MeasureExpr -> do
        let qlist = exprAsQlist (children !! 0)
        return $ WSeq c $ map (WMeasure c . pretty) $ qlist
      -- [element..]
      List -> mapM go children >>= return . WSeq c
      _ -> return $ WSkip c

-- Applies a substitution list generated by phase folding
applyPFOpt :: Map Loc Angle -> Node Tag Loc -> Node Tag Loc
applyPFOpt replacements node = go node
  where
    go NilNode = NilNode
    go node@(Node GateCallStmt children l) = case Map.lookup l replacements of
      Nothing -> node
      Just theta -> makeTheta theta children l
    go node@(Node tag children l) =
      let children' = map go children
       in Node tag children' l

    makeTheta theta (m : _ : args) l =
      let prim = synthesizePhase "-" theta
       in case prim of
            [] -> NilNode
            [x] -> Node GateCallStmt (m : (makeIdent $ nameOfGate x) : args) l

    makeIdent str = Node (Identifier str (IdentifierToken str)) [] 0

    nameOfGate gate = case gate of
      Rz theta _ -> "rz(" ++ show theta ++ ")"
      Z _ -> "z"
      S _ -> "s"
      Sinv _ -> "sdg"
      T _ -> "t"
      Tinv _ -> "tdg"

-- Applies a While statement optimization to a qasm 3 program
applyWStmtOpt :: ([ID] -> [ID] -> WStmt Loc -> Map Loc Angle) -> Node Tag Loc -> Node Tag Loc
applyWStmtOpt opt node = result
  where
    node' = decorateIDs node -- recompute to make sure IDs are unique
    wstmt = simplifyWStmt' $ buildModel node'
    vlst = idsW wstmt
    result = applyPFOpt (opt vlst vlst wstmt) node'

-- Counts qubits
countQubits :: Node Tag c -> Int
countQubits node = length vlst
  where
    vlst = idsW . buildModel . decorateIDs $ node

-- Counts gate calls
countGateCalls :: Node Tag c -> Map String Int
countGateCalls node = go Map.empty node
  where
    go counts NilNode = counts
    go counts node@(Node GateStmt _ _) = counts
    go counts node@(Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c) =
      let id = getIdent target
       in case id of
            "x" -> Map.insertWith (+) "X" 1 counts
            "y" -> Map.insertWith (+) "Y" 1 counts
            "z" -> Map.insertWith (+) "Z" 1 counts
            "h" -> Map.insertWith (+) "H" 1 counts
            "t" -> Map.insertWith (+) "T" 1 counts
            "tdg" -> Map.insertWith (+) "T" 1 counts
            "s" -> Map.insertWith (+) "S" 1 counts
            "sdg" -> Map.insertWith (+) "S" 1 counts
            "cx" -> Map.insertWith (+) "cnot" 1 counts
            "ccx" -> Map.unionWith (+) counts $ Map.fromList [("H", 2), ("cnot", 7), ("T", 7)]
            _ -> Map.insertWith (+) id 1 counts
    go counts (Node tag children c) = foldl go counts children

-- Print out stats
showStats :: Node Tag c -> [String]
showStats node = qubitCounts ++ gateCounts
  where
    qubitCounts = ["Qubits: " ++ show (countQubits node)]
    gateCounts = (map f . Map.toList) $ countGateCalls node
    f (gate, count) = gate ++ ": " ++ show count
