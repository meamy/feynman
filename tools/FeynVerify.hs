{-# LANGUAGE TupleSections #-}
module Main (main) where

import Feynman.Core (Primitive(CNOT, T, Tinv), ID)
import Feynman.Frontend.DotQC
import Feynman.Verification.SOP

import System.Environment
import System.Time
import Numeric

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid hiding ((<>))
import Data.Semigroup

import Control.Monad
import Control.DeepSeq

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

equivalenceCheck options src src' = do
  qc  <- parseDotQC src
  qc' <- parseDotQC src'
  return $ ver qc qc'
  where ver qc qc' =
          let gates  = toCliffordT . toGatelist $ qc
              gates' = toCliffordT . toGatelist $ qc'
              vars   = union (qubits qc) (qubits qc')
              ins    = Set.toList $ inputs qc
              ignore = Set.member "IgnoreGlobal" options
              result =
                if Set.member "IgnoreGarbage" options
                then validateOnInputs ignore vars ins gates gates'
                else if Set.member "Postselect" options
                  then validateToScale ignore vars ins gates gates'
                  else validateIsometry ignore vars ins gates gates'
          in
            if inputs qc /= inputs qc'
            then NotIdentity "Inputs don't match"
            else result

getSOP src = do
  qc  <- parseDotQC src
  let init = blank (qubits qc \\ Set.toList (inputs qc))
  let sop = circuitSOP . toCliffordT . toGatelist $ qc
  return . reduce $ init <> sop 

{- Main program -}

printHelp :: IO ()
printHelp = mapM_ putStrLn lines
  where lines = [
          "Feynver -- quantum circuit equivalence checker",
          "Written by Matthew Amy",
          "",
          "Usage: feynver [options] <circuit1>.qc <circuit2>.qc",
          "",
          "Options:",
          "  -ignore-global-phase\tVerify equivalence up to a global phase",
          "  -ignore-ancillas\tVerify equivalence up to (separable) garbage in the ancilla qubits",
          "  -postselect-ancillas\tVerify equivalence, post-selecting on the ancillas being in the 0 state",
          ""
          ]

printResult result time = case result of
  Identity pf -> do
    putStrLn $ "Equal (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Proof:"
    mapM_ (\rl -> putStrLn $ "  " ++  show rl) pf
  NotIdentity ce -> do
    putStrLn $ "Not equal (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Reason:"
    putStrLn $ "  " ++ ce
  Unknown sop -> do
    putStrLn $ "Inconclusive (took " ++ formatFloatN time 3 ++ "ms)"
    putStrLn $ "Residual path sum:"
    putStrLn $ "  " ++ show sop

run :: Set String -> [String] -> IO ()
run options (x:[])
  | (drop (length x - 3) x == ".qc") = do
      xsrc <- B.readFile x
      case getSOP xsrc of
        Left l    -> putStrLn $ show l
        Right sop -> putStrLn $ show sop
run options (x:y:[])
  | (drop (length x - 3) x == ".qc") && (drop (length y - 3) y == ".qc") = do
      xsrc <- B.readFile x
      ysrc <- B.readFile y
      TOD starts startp <- getClockTime
      let result        = equivalenceCheck options xsrc ysrc
      TOD ends endp     <- result `seq` getClockTime
      let time = (fromIntegral $ ends - starts) * 1000 + (fromIntegral $ endp - startp) / 10^9
      case result of
        Left l         -> putStrLn $ show l
        Right (result) -> printResult result time
run options (x:xs)
  | x == "-ignore-global-phase" = run (Set.insert "IgnoreGlobal" options) xs
  | x == "-ignore-ancillas"     = run (Set.insert "IgnoreGarbage" options) xs
  | x == "-postselect-ancillas" = run (Set.insert "Postselect" options) xs
run _ _ = do
      putStrLn "Invalid argument(s)"
      printHelp

main :: IO ()
main = getArgs >>= run Set.empty
