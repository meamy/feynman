module Feynman.Simulation.PathsumVerification where

import Feynman.Algebra.Pathsum.Balanced hiding (Var, Zero)
import Feynman.Frontend.OpenQASM.Syntax
import Feynman.Simulation.Env
import Feynman.Simulation.PathsumSpecification
import Feynman.Simulation.Pathsum

import qualified Debug.Trace as Trace

verifyProg' :: Spec -> Env -> Bool
verifyProg' spec env =
  let mask       = channelize $ createAncillaMask spec
      specPs     = grind $ channelize $ sopOfPSSpec spec env
      initPS     = identity (inDeg mask)
      progPS     = case density env of
        False -> conjugate (pathsum env) <> pathsum env
        True  -> pathsum env
      traceBinds = traceList (fst . unzip $ inputs spec) env
      tracedPS   = grind $ foldl (\ps (i, idx) -> traceOut idx (idx+m-i) ps) progPS $ zip [0..] traceBinds
      bindings   = bindingList (inputs spec) env
      closedPS   = bind (map ("'" ++) bindings ++ bindings) tracedPS
      n          = inDeg specPs
      m          = case density env of
        False -> outDeg (pathsum env)
        True -> outDeg (pathsum env) `div` 2
  in
    Trace.trace (show . grind $ progPS) $
      (dropAmplitude $ grind $ mask .> closedPS .> (dagger (mask .> specPs))) == initPS

verifyQASM :: QASM -> Env
verifyQASM prog@(QASM _ (Just spec) stmts) =
  let env = simQASM' prog (Just $ initEnv { density = True, uninitialized = inputs spec })
      result = case verifyProg' spec env of
        False -> "Failed!"
        True  -> "Success!"
  in
  Trace.trace ("Verifying whole program against specification " ++ (show $ sopOfPSSpec spec env) ++ "..." ++ result) $ env

