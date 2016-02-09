module Syntax (parseQC, printCircIR) where

import Text.ParserCombinators.Parsec
import Data.Map (Map)
import qualified Data.Map as Map

data PrimGate =
    H    String
  | X    String
  | Y    String
  | CNOT String String
  | Rz Int String Int String

data Stmt =
    Gate PrimGate
  | Seq [Stmt]
  | Call String [String]
  | Repeat Int Stmt
   
data Circuit = Circuit { name   :: String,
                         params :: [String],
                         body   :: Stmt }
 
data CircuitIR = CircuitIR { qubits   :: [String],
                             inputs   :: Map String Bool,
                             circuits :: [Circuit] }

foldCirc f c b = foldr (\c -> foldStmt f (body c)) b (circuits c)

foldStmt f (Seq st)      b = f (Seq st) (foldr (foldStmt f) b st)
foldStmt f (Repeat i st) b = f (Repeat i st) (foldStmt f st b)
foldStmt f s             b = f s b

calls c = foldCirc f c [] -- concatMap (\c -> foldStmt f (body c) []) (circuits c)
  where f (Call id _) b = (id:b)
        f _ b           = b

ids c = foldCirc f c [] --concatMap (\c -> foldStmt f (body c) []) (circuits c)
  where f (Call id _) b = (id:b)
        f _ b           = b

-- Printing

instance Show PrimGate where
  show (H id) = "H " ++ (show id)
  show (X id) = "X " ++ (show id)
  show (Y id) = "Y " ++ (show id)
  show (CNOT id1 id2) = "tof " ++ (show id1) ++ " " ++ (show id2)
  show (Rz mu ph pow id) = formatPhase mu ph pow ++ " " ++ (show id)

formatPhase 1    "pi" 2  = "T"
formatPhase (-1) "pi" 2  = "T*"
formatPhase 1    "pi" 1  = "P"
formatPhase (-1) "pi" 1  = "P*"
formatPhase 1    "pi" 0  = "Z"
formatPhase (-1) "pi" 0  = "Z*"
formatPhase 1    str pow = "Rz(" ++ (show str) ++ "/2^" ++ (show pow) ++ ")"
formatPhase (-1) str pow = "Rz(-" ++ (show str) ++ "/2^" ++ (show pow) ++ ")"
formatPhase mu   str pow = "Rz(" ++ (show mu) ++ (show str) ++ "/2" ++ (show pow) ++ ")"

printStmt stmt = case stmt of
    Gate gate -> putStrLn $ show gate
    Seq lst -> sequence_ $ map printStmt lst
    Call id args -> putStrLn $ (show id) ++ (printLst args)
    Repeat i (Call id args) -> putStrLn $ (show id) ++ "^" ++ (show i) ++ (printLst args)
    Repeat i stmt -> putStrLn ("Begin^" ++ (show i)) >> printStmt stmt >> putStrLn "End"

printCirc circ = do
    putStrLn $ "BEGIN " ++ (putName (name circ)) ++ (printLst (params circ))
    printStmt (body circ)
    putStrLn $ "END"
    where putName "main" = ""
          putName s      = s

printCircIR circIR = do
    putStrLn  $ ".v" ++ (printLst (qubits circIR))
    putStrLn  $ ".i" ++ (printLst (filter (\t -> Map.notMember t (inputs circIR)) (qubits circIR)))
    sequence_ $ (map (\circ -> putStrLn "" >> printCirc circ) (circuits circIR))
    
printLst lst = reverse $ foldr (\ x l -> x ++ " " ++ l) "" lst

-- Parsing
semicolon = char ';'
sep = space <|> newline <|> tab <|> semicolon
parseToken s = string s >> space >> skipMany space >> return s
parseCircuitID = letter >>= \c -> many alphaNum >>= \cs -> skipMany space >> return (c:cs)
parseArgList = sepBy (many1 alphaNum) (many1 space) 
parseIDlst :: Int -> Parser [String]
parseIDlst n = count n (many1 alphaNum >>= \id -> skipMany space >> return id)
parsePhase = do
  char '('
  m <- integer
  char '*'
  s <- many alphaNum
  char '/'
  d <- natural
  char ')'
  return (m, s, d)
  where integer = do s <- option "" (string "-")
                     i <- many digit
                     return $ read (s ++ i)
        natural = many digit >>= return . read

parseGate =
  (parseToken "H" >> parseIDlst 1 >>= \lst -> return $ H (lst !! 1)) <|>
  (parseToken "X" >> parseIDlst 1 >>= \lst -> return $ X (lst !! 1)) <|>
  (parseToken "Y" >> parseIDlst 1 >>= \lst -> return $ Y (lst !! 1)) <|>
  (parseToken "Z" >> parseIDlst 1 >>= \lst -> return $ Rz 1 "pi" 0 (lst !! 1)) <|>
  (parseToken "P" >> parseIDlst 1 >>= \lst -> return $ Rz 1 "pi" 1 (lst !! 1)) <|>
  (parseToken "P*" >> parseIDlst 1 >>= \lst -> return $ Rz (-1) "pi" 1 (lst !! 1)) <|>
  (parseToken "T" >> parseIDlst 1 >>= \lst -> return $ Rz 1 "pi" 2 (lst !! 1)) <|>
  (parseToken "T*" >> parseIDlst 1 >>= \lst -> return $ Rz (-1) "pi" 2 (lst !! 1)) <|>
  ((parseToken "tof" <|> parseToken "cnot") >> parseIDlst 2 >>= \lst -> return $ CNOT (lst !! 1) (lst !! 2)) <|>
  (parseToken "Rz" >> parsePhase >>= \(m, s, d) -> parseIDlst 1 >>= \lst -> return $ Rz m s d (lst !! 1)) 

parseStmt = (try parseGate >>= return . Gate)-- <|> (try parseCall) <|> (try parseRepeat)
parseStmtSeq = sepBy parseStmt (many1 (semicolon <|> newline)) >>= return . Seq

parseCircuit = do
  parseToken "BEGIN"
  id <- option "main" (try parseCircuitID)
  args <- parseArgList
  skipMany sep
  stmt <- parseStmtSeq
  skipMany sep
  parseToken "END"
  skipMany sep
  return $ Circuit id args stmt

parseFile = do
  skipMany sep
  parseToken ".v"
  qubits <- parseArgList
  skipMany sep
  parseToken ".i"
  primaryInputs <- parseArgList
  skipMany sep
  circs <- many1 (try (parseCircuit))
  return $ genCircuitIR qubits primaryInputs circs
  where genCircuitIR q p c =
          let zeros = filter (\id -> not (elem id p)) q in
            CircuitIR q (foldr (\id -> Map.insert id False) Map.empty zeros) c

parseQC = parse parseFile ".qc parser" 

-- Semantic analysis
{-
analyze circuit = do
  verifyMultDef
  verifyCallIDs
  verifyQubitIDs
  where qubitIDs      = qubits circuit
        circuitIDs    = map name (circuits circuit)
        f lst id      = case elem id lst of
                          True -> Left "Error: " ++ id ++ " defined multiple times"
                          False -> Right (id:lst)
        verifyMultDef = foldM f [] (qubitIDs ++ circuitIDs)
        verifyCallIDs = foldM g "" calls
-}

{-
main = do
  c <- getContents
  case parse parseFile ".qc parser" c of
    Left err -> putStrLn $ "Error parsing input: " ++ show err
    Right circuit -> printCircIR circuit -- putStrLn "Calls:" >> sequence_ (map (putStrLn . show) (calls circuit))
-}
