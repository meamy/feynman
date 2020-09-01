{-# LANGUAGE TupleSections #-}
module Main (main) where

import Control.Monad.Trans.Class  (lift)
import Control.Monad.Trans.Except (ExceptT(..), runExceptT, except)
import System.Environment         (getArgs)
import System.CPUTime             (getCPUTime)
import Data.List                  (takeWhile, union, (\\))
import Data.Set                   (Set)
import Data.Semigroup             ((<>))
import Text.Printf                (printf)
import Text.Parsec                (ParseError)

import qualified Data.ByteString as B
import qualified Data.Set as Set

import Feynman.Core hiding (inputs, qubits, getArgs)
import Feynman.Frontend.DotQC
import Feynman.Verification.SOP

-- | Check whether two .qc files are equivalent
checkEquivalence :: Set String -> (DotQC, DotQC) -> VerificationResult Z8
checkEquivalence options (qc, qc') =
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
  
-- | Get the (reduced) path sum of a DotQC circuit
getSOP :: DotQC -> SOP Z8
getSOP qc = snd . reduce $ init <> sop where
  init = blank $ qubits qc \\ Set.toList (inputs qc)
  sop  = circuitSOP . toCliffordT . toGatelist $ qc

-- | Get the extension of a filename
extension :: String -> String
extension = reverse . takeWhile (/= '.') . reverse

-- | Print the menu
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

-- | Format the verification result
formatResult :: VerificationResult Z8 -> Double -> String
formatResult result time = case result of
  Identity _pf    -> printf "Equal (took %.3fs)" time
  NotIdentity _ce -> printf "Not equal (took %.3fs)" time
  Unknown sop     -> printf "Inconclusive (took %.3fs)" time ++
                     "\nReduced form: \n" ++ show sop

-- | Time a computation
withTiming :: (a -> b) -> a -> IO (b, Double)
withTiming f a = do
  start <- getCPUTime
  let res = f a
  res `seq` return ()
  end   <- getCPUTime
  return (res, (fromIntegral $ end - start) / 10^12)

-- | Print an Either
printError :: Either ParseError String -> IO ()
printError (Left err) = print err
printError (Right st) = putStrLn st

-- | Main program
run :: Set String -> [String] -> ExceptT ParseError IO String
run options xs = case xs of
  [x]    | extension x == "qc" -> do
             xsrc <- lift $ B.readFile x
             qc <- ExceptT $ return $ parseDotQC xsrc
             return . show $ getSOP qc
  [x,y]  | extension x == "qc" && extension y == "qc" -> do
             xsrc <- lift $ B.readFile x
             ysrc <- lift $ B.readFile y
             qc   <- ExceptT $ return $ parseDotQC xsrc
             qc'  <- ExceptT $ return $ parseDotQC ysrc
             (res, time) <- lift $ withTiming (checkEquivalence options) (qc,qc')
             return $ formatResult res time
  (x:xs) | x == "-ignore-global-phase" -> run (Set.insert "IgnoreGlobal" options) xs
         | x == "-ignore-ancillas"     -> run (Set.insert "IgnoreGarbage" options) xs
         | x == "-postselect-ancillas" -> run (Set.insert "PostSelect" options) xs
  _ -> do
    lift $ putStrLn "Invalid argument(s)"
    lift $ printHelp
    return ""

main :: IO ()
main = do
  args   <- getArgs
  result <- runExceptT $ run Set.empty args
  printError result
