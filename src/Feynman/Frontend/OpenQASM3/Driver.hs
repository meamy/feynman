module Feynman.Frontend.OpenQASM3.Driver where

import Control.Monad.State.Lazy
import Data.Int (Int64)
-- import qualified Data.Map.Strict as Map
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import Debug.Trace (trace)
import Feynman.Algebra.Base
import Feynman.Core hiding (Decl, subst)
import Feynman.Frontend.OpenQASM3.Ast
import qualified Feynman.Frontend.OpenQASM3.Chatty as Chatty
import Feynman.Frontend.OpenQASM3.Semantics
import Feynman.Frontend.OpenQASM3.Syntax
import Feynman.Synthesis.Phase

-- type Ctx = Map.Map String SyntaxNode

type Result c = Chatty.Chatty String String c

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
applyPFOpt replacements node = pruneEmptyStatements (go node)
  where
    go NilNode = NilNode
    go node@(Node GateCallStmt [NilNode, ident, args, NilNode, operands] l) = case Map.lookup l replacements of
      Nothing -> node
      Just theta -> makeTheta theta operands l
    go node@(Node GateCallStmt _ _) = error "GateCallStmt we can't process"
    go node@(Node tag children l) =
      let children' = map go children
       in Node tag children' l
    makeTheta theta operands l =
      let prim = synthesizePhase "-" theta
       in case prim of
            [] -> NilNode
            [x] ->
              let nameNode = withContext (-1) (identifierNode (nameOfGate x))
                  params = map (withContext (-1)) (paramsOfGate x)
                  paramsNode = if null params then NilNode else Node List params (-1)
               in Node
                    GateCallStmt
                    [NilNode, nameNode, paramsNode, NilNode, operands]
                    l

    nameOfGate gate =
      case gate of
        Rz _ _ -> "rz"
        Z _ -> "z"
        S _ -> "s"
        Sinv _ -> "sdg"
        T _ -> "t"
        Tinv _ -> "tdg"

    paramsOfGate (Rz theta _) = [exprFromAngle theta]
    paramsOfGate _ = []

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

-- Counts gate calls
countGateCalls :: Node Tag c -> Map String Int
countGateCalls node = go Map.empty node
  where
    go counts NilNode = counts
    go counts node@(Node GateCallStmt [modifiers, target, params, maybeTime, gateArgs] c) =
      let id = getIdent target
       in Map.insertWith (+) id 1 counts
    go counts (Node tag children c) = foldl go counts children

{-
-- transcribed from the OpenQASM 3.0 standard gate library and qelib1.inc

-- stdgates definitions not in qelib1
gate p(λ) a { ctrl @ gphase(λ) a; }
gate sx a { pow(0.5) @ x a; }
gate crx(θ) a, b { ctrl @ rx(θ) a, b; }
gate cry(θ) a, b { ctrl @ ry(θ) a, b; }
gate swap a, b { cx a, b; cx b, a; cx a, b; }
gate cswap a, b, c { ctrl @ swap a, b, c; }
gate cp(λ) a, b { ctrl @ p(λ) a, b; }
gate phase(λ) q { U(0, 0, λ) q; } -- same as u1
gate cphase(λ) a, b { ctrl @ phase(λ) a, b; } -- controlled u1

-- and because it's a QASM2 builtin,
gate CX a, b { ctrl @ U(π, 0, π) a, b; }

-- qelib1 has cu1 not in stdgates
gate cu1(lambda) a,b
{
  u1(lambda/2) a;
  cx a,b;
  u1(-lambda/2) b;
  cx a,b;
  u1(lambda/2) b;
}

-- stdgates definition
gate x a { U(π, 0, π) a; gphase(-π/2);}
-- qelib1 definition
gate x a { u3(pi,0,pi) a; }

-- stdgates definition
gate y a { U(π, π/2, π/2) a; gphase(-π/2);}
-- qelib1 definition
gate y a { u3(pi,pi/2,pi/2) a; }

-- stdgates definition
gate z a { p(π) a; }
-- qelib1 definition
gate z a { u1(pi) a; }

-- stdgates definition
gate h a { U(π/2, 0, π) a; gphase(-π/4);}
-- qelib1 definition
gate h a { u2(0,pi) a; }

-- stdgates definition
gate s a { pow(0.5) @ z a; }
-- qelib1 definition
gate s a { u1(pi/2) a; }

-- stdgates definition
gate sdg a { inv @ pow(0.5) @ z a; }
-- qelib1 definition
gate sdg a { u1(-pi/2) a; }

-- stdgates definition
gate t a { pow(0.5) @ s a; }
-- qelib1 definition
gate t a { u1(pi/4) a; }

-- stdgates definition
gate tdg a { inv @ pow(0.5) @ s a; }
-- qelib1 definition
gate tdg a { u1(-pi/4) a; }

-- stdgates definition
gate rx(θ) a { U(θ, -π/2, π/2) a; gphase(-θ/2);}
-- qelib1 definition
gate rx(theta) a { u3(theta,-pi/2,pi/2) a; }

-- stdgates definition
gate ry(θ) a { U(θ, 0, 0) a; gphase(-θ/2);}
-- qelib1 definition
gate ry(theta) a { u3(theta,0,0) a; }

-- stdgates definition
gate rz(λ) a { gphase(-λ/2); U(0, 0, λ) a; }
-- qelib1 definition
gate rz(phi) a { u1(phi) a; }

-- stdgates definition
gate cx a, b { ctrl @ x a, b; }
-- qelib1 definition
gate cx c,t { CX c,t; }

-- stdgates definition
gate cy a, b { ctrl @ y a, b; }
-- qelib1 definition
gate cy a,b { sdg b; cx a,b; s b; }

-- stdgates definition
gate cz a, b { ctrl @ z a, b; }
-- qelib1 definition
gate cz a,b { h b; cx a,b; h b; }

-- stdgates definition
gate crz(θ) a, b { ctrl @ rz(θ) a, b; }
-- qelib1 definition
gate crz(lambda) a,b
{
  u1(lambda/2) b;
  cx a,b;
  u1(-lambda/2) b;
  cx a,b;
}

-- stdgates definition
gate ch a, b { ctrl @ h a, b; }
-- qelib1 definition
gate ch a,b {
h b; sdg b;
cx a,b;
h b; t b;
cx a,b;
t b; h b; s b; x b; s a;
}

-- stdgates definition
gate ccx a, b, c { ctrl @ ctrl @ x a, b, c; }
-- qelib1 definition
gate ccx a,b,c
{
  h c;
  cx b,c; tdg c;
  cx a,c; t c;
  cx b,c; tdg c;
  cx a,c; t b; t c; h c;
  cx a,b; t a; tdg b;
  cx a,b;
}

-- stdgates definition
gate cu(θ, φ, λ, γ) a, b { p(γ-θ/2) a; ctrl @ U(θ, φ, λ) a, b; }
-- qelib1 definition
gate cu3(theta,phi,lambda) c, t
{
  // implements controlled-U(theta,phi,lambda) with  target t and control c
  u1((lambda-phi)/2) t;
  cx c,t;
  u3(-theta/2,0,-(phi+lambda)/2) t;
  cx c,t;
  u3(theta/2,phi,0) t;
}

-- stdgates definition
gate id a { U(0, 0, 0) a; }
-- qelib1 definition
gate id a { U(0,0,0) a; }

-- stdgates definition
gate u1(λ) q { U(0, 0, λ) q; }
-- qelib1 definition
gate u1(lambda) q { U(0,0,lambda) q; }

-- stdgates definition
gate u2(φ, λ) q { gphase(-(φ+λ+π/2)/2); U(π/2, φ, λ) q; }
-- qelib1 definition
gate u2(phi,lambda) q { U(pi/2,phi,lambda) q; }

-- stdgates definition
gate u3(θ, φ, λ) q { gphase(-(φ+λ+θ)/2); U(θ, φ, λ) q; }
-- qelib1 definition
gate u3(theta,phi,lambda) q { U(theta,phi,lambda) q; }

-- in both QASM2 and QASM3, U(...) a la u3(...) is a builtin

-}
