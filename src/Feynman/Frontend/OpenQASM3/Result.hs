module Frontend.OpenQASM3.Result where

import Frontend.OpenQASM3.Chatty

newtype Failure = Failure {failMessage :: String} deriving (Eq, Read, Show)

type Result a = Chatty String Failure a

failResult :: String -> Result a
failResult errMsg = ChattyFailure ["Error: " ++ errMsg] (Failure errMsg)

addResultMessage :: String -> Result ()
addResultMessage msg = ChattyValue [msg] ()

