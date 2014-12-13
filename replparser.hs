module Main where

import Control.Monad
import System.Environment
import Control.Monad.Error 
import Text.ParserCombinators.Parsec hiding (spaces)
import System.IO hiding (try)


-- gets arguments provided by user. Runs REPL if no arguments, evaluates and prints if one argument. Throws error otherwise.
main :: IO ()
main = do args <- getArgs
          case length args of
              0 -> runRepl
              1 -> evalAndPrint (args !! 0)
              otherwise -> putStrLn "Program takes only 0 or 1 argument"

-- data declaration for the different supported Scheme data types.
data LispVal = Atom String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | String String
             | Bool Bool

-- parser that is successful if the symbol being parsed is in the string below. Uses the Parsec parse function oneOf. 
symbol :: Parser Char
symbol = oneOf "!$%&|*+-/:<=?>@^_~#"

-- uses the Parsec function parse to parse the input string. Throws an error if the function returns something of 
-- type Left, and returns the parsed value (wrapped in a ThrowsError monad) if parsing was successful.
readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
    Left err -> throwError $ Parser err
    Right val -> return val

-- parser that skips any leading spaces.
spaces :: Parser ()
spaces = skipMany1 space

-- parses a string. String must start and end with quotation marks.
parseString :: Parser LispVal
parseString = do char '"'
                 x <- many (noneOf "\"")
                 char '"'
                 return $ String x

-- parses an atom, using Parsec parsers letter, symbol, many, and digit. 
parseAtom :: Parser LispVal
parseAtom = do first <- letter <|> symbol
               rest <- many (letter <|> digit <|> symbol)
               let atom = [first] ++ rest
               return $ case atom of 
                          "#t" -> Bool True
                          "#f" -> Bool False
                          otherwise -> Atom atom

-- parses a number. This originally used liftM but we changed it to use a bind.
parseNumber :: Parser LispVal
parseNumber = (many1 digit) >>= (return . Number . read)

-- parses a list. Scheme statements are all lists, e.g. (+ 1 1 1), which is evaluated to 3. We changed liftM to bind here also.
parseList :: Parser LispVal
parseList = (sepBy parseExpr spaces) >>= (return . List)

-- parses a dotted list, such as (1 2 . 3)
parseDottedList :: Parser LispVal
parseDottedList = do
    head <- endBy parseExpr spaces
    tail <- char '.' >> spaces >> parseExpr
    return $ DottedList head tail

-- parses an expression that starts with a quotation mark, such as '(a 2 b) (this is the list data type), or 'a (the atom a) 
parseQuoted :: Parser LispVal
parseQuoted = do
    char '\''
    x <- parseExpr
    return $ List [Atom "quote", x]

-- uses the parsers defined earlier; <|> means try the first one, and try the second one if it fails, and so on. 
-- this parser is used by readExpr (defined above)
parseExpr :: Parser LispVal
parseExpr = parseAtom
        <|> parseString
        <|> parseNumber
        <|> parseQuoted
        <|> do char '('
               x <- (try parseList) <|> parseDottedList
               char ')'
               return x

-- converts Lispvals to strings that can be printed
showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Atom name) = name
showVal (Number contents) = show contents
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (List contents) = "(" ++ unwordsList contents ++ ")"
showVal (DottedList head tail) = "(" ++ unwordsList head ++ " . " ++ showVal tail ++ ")"

-- A list of Lispvals is evaluated and then joined together using spaces. 
-- For example [Number 2, Number 3] becomes "2 3". Parens are added in showVal above, so we get (2 3). 
unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

-- we declare Lispval as an instance of Show so that we get string representations of LispVals
instance Show LispVal where show = showVal

-- evaluates the LispVal. Primitives such as Numbers, Strings, Bools and quoted Lists are evaluated to themselves. For 
-- operations we need to do a lookup in the primitives list. We throw an error if we do not recognize the parsed form.
eval :: LispVal -> ThrowsError LispVal
eval (String a) = return (String a)
eval val@(Number _) = return val 
eval val@(Bool _) = return val
eval (List [Atom "quote", val]) = return val
eval (List [Atom "if", pred, conseq, alt]) = 
    do result <- eval pred
       case result of
         Bool False -> eval alt
         otherwise -> eval conseq
eval (List (Atom func : args)) = mapM eval args >>= apply func
eval badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

-- uses the maybe function. Tries (lookup func primitives). If successful, applies the function to args. 
-- if unsucessful, an error is thrown.
apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe (throwError $ NotFunction "Unrecognized primitive function args" func)
                        ($ args)
                        (lookup func primitives)


-- Lookup table, in which Scheme operators and special forms are mapped to partially applied Haskell functions. Used for evaluation.
primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [("+", numericBinop (+)),
              ("-", numericBinop (-)),
              ("*", numericBinop (*)),
              ("/", numericBinop div),
              ("mod", numericBinop mod),
              ("quotient", numericBinop quot),
              ("remainder", numericBinop rem),
              ("=", numBoolBinop (==)),
              ("<", numBoolBinop (<)),
              (">", numBoolBinop (>)),
              ("/=", numBoolBinop (/=)),
              (">=", numBoolBinop (>=)),
              ("<=", numBoolBinop (<=)),
              ("&&", boolBoolBinop (&&)),
              ("||", boolBoolBinop (||)),
              ("string=?", strBoolBinop (==)),
              ("string?", strBoolBinop (>)),
              ("string<=?", strBoolBinop (<=)),
              ("string>=?", strBoolBinop (>=)),
              ("car", car),
              ("cdr", cdr),
              ("cons", cons),
              ("eq?", eqv),
              ("eqv?", eqv),
              ("equal?", equal)]

-- applies the numeric binary operation op to the list of LispVals using a left fold. 
numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params = mapM unpackNum params >>= (return . Number . foldl1 op)

-- uses the comparison operation op to compare the args, after unpacking the LispVals. 
boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2 
                             then throwError $ NumArgs 2 args
                             else do left <- unpacker $ args !! 0
                                     right <- unpacker $ args !! 1
                                     return $ Bool $ left `op` right

-- definining the operations as partial applications
numBoolBinop = boolBinop unpackNum
strBoolBinop = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool

-- "unpacks" the Haskell Integer from the Lispval so that Haskell can do numeric operations. Wrapped in ThrowsError container
-- so that errors can be thrown
unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in 
                          if null parsed 
                            then throwError $ TypeMismatch "number" $ String n
                            else return $ fst $ parsed !! 0
unpackNum (List [n]) = unpackNum n
unpackNum notNum = throwError $ TypeMismatch "number" notNum

-- "unpacks" the Haskell String from the LispVal. 
unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr (Number s) = return $ show s
unpackStr (Bool s) = return $ show s
unpackStr notString = throwError $ TypeMismatch "string" notString

-- "unpacks"
unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool = throwError $ TypeMismatch "boolean" notBool

-- defines the Scheme function "car", which is equivalent to Haskell's "head" for lists
car :: [LispVal] -> ThrowsError LispVal
car [List (x : xs)] = return x
car [DottedList (x : xs) _] = return x
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

-- defines the Scheme function "cdr", which is equivalent to Haskell's "tail" for lists
cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (x : xs)] = return $ List xs
cdr [DottedList (_ : xs) x] = return $ DottedList xs x
cdr [DottedList [xs] x] = return x
cdr [badArg] = throwError $ TypeMismatch "pair" badArg
cdr badArgList = throwError $ NumArgs 1 badArgList

-- defines the Scheme function cons, equivalent to the Haskell (:)
cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []] = return $ List [x1]
cons [x, List xs] = return $ List $ [x] ++ xs
cons [x, DottedList xs xlast] = return $ DottedList ([x] ++ xs) xlast
cons [x1, x2] = return $ DottedList [x1] x2
cons badArgList = throwError $ NumArgs 2 badArgList

-- defines the special form eqv?. The special form eq? also uses this (see primitives)
eqv :: [LispVal] -> ThrowsError LispVal
eqv [(Bool arg1), (Bool arg2)] = return $ Bool $ arg1 == arg2
eqv [(Number arg1), (Number arg2)] = return $ Bool $ arg1 == arg2
eqv [(String arg1), (String arg2)] = return $ Bool $ arg1 == arg2
eqv [(Atom arg1), (Atom arg2)] = return $ Bool $ arg1 == arg2
eqv [(DottedList xs x), (DottedList ys y)] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
eqv [(List arg1), (List arg2)] = return $ Bool $ (length arg1 == length arg2) && 
                                                    (and $ map eqvPair $ zip arg1 arg2)
    where eqvPair (x1, x2) = case eqv [x1, x2] of
                               Left err -> False
                               Right (Bool val) -> val
eqv [_, _] = return $ Bool False
eqv badArgList = throwError $ NumArgs 2 badArgList

-- data declaration for Unpacker. This uses the Existential Types extension that allows heterogenous lists.
-- This says that for any type that is an instance of Eq we can define an Unpacker 
-- that takes a function from LispVal to that type, and may throw an error
data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

-- Implements the unpacker for the special form "equals?". "unpacker" used to unpack the two args,
-- and then they are compared. String "2" and Number 2 are both unpacked to 2, so they are equal
unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = 
             do unpacked1 <- unpacker arg1
                unpacked2 <- unpacker arg2
                return $ unpacked1 == unpacked2
        `catchError` (const $ return False)

-- implements the special form "equal?
equal :: [LispVal] -> ThrowsError LispVal
equal [arg1, arg2] = do
    primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2) 
                      [AnyUnpacker unpackNum, AnyUnpacker unpackStr, AnyUnpacker unpackBool]
    eqvEquals <- eqv [arg1, arg2]
    return $ Bool $ (primitiveEquals || let (Bool x) = eqvEquals in x)
equal badArgList = throwError $ NumArgs 2 badArgList

-- data declaration for LispErrors that can be thrown
data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | Parser ParseError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String

-- function that converts LispErrors to Strings that can be shown
showError :: LispError -> String
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func) = message ++ ": " ++ show func
showError (NumArgs expected found) = "Expected " ++ show expected 
                                  ++ " args: found values " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected
                                       ++ ", found " ++ show found
showError (Parser parseErr) = "Parse error at " ++ show parseErr

-- LispError declared as an instance of Show so that they can be represented for the user
instance Show LispError where show = showError

-- LispError declared an instance of Error, from Control.Monad.Error (built-in module)
instance Error LispError where
     noMsg = Default "An error has occurred"
     strMsg = Default

-- type declaration for ThrowsError, which is a partial application of the Either data type.
-- ThrowsError val is thus the same as Either LispError val. Thus if there's an error, LispError is thrown,
-- else expression is evaluated to val.
type ThrowsError = Either LispError

-- uses the built-in catchError function to catch errors
trapError action = catchError action (return . show)

-- simply extracts the value wrapped in ThrowsError
extractValue :: ThrowsError a -> a
extractValue (Right val) = val

-- String is printed out to stdout 
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

-- string is flushed out to stdout, and user command is read in
readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

-- simple loop using weak bind. Used in runRepl below.
until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
  result <- prompt
  if pred result 
     then return ()
     else  action result >> until_ pred prompt action

-- uses until_ to create the read-eval-print loop (REPL). 
runRepl :: IO ()
runRepl = until_ (== "quit") (readPrompt "Lisp>>> ") evalAndPrint

-- evaluates the expression using evalString and prints it out.
evalAndPrint :: String -> IO ()
evalAndPrint expr =  evalString expr >>= putStrLn

-- parses the expression, evaluates it, extracts the value from the ThrowsError type and returns an IO string
-- that used by evalAndPrint to print out an answer.
evalString :: String -> IO String
evalString expr = return $ extractValue $ trapError ((readExpr expr >>= eval) >>= (return . show))

{-

Various definitions of built-in functions / functions and combinators from the Parsec library:

data  Either a b  =  Left a | Right b   deriving (Eq, Ord, Read, Show)

unwords          :: [String] -> String
unwords []       =  ""
unwords ws       =  foldr1 (\w s -> w ++ ' ':s) ws

mapM             :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f as        =  sequence (map f as)

sequence :: Monad m => [m a] -> m [a]

-- and returns the conjunction of a Boolean list.  For the result to be
-- True, the list must be finite; False, however, results from a False
-- value at a finite index of a finite or infinite list.  or is the
-- disjunctive dual of and.

and, or          :: [Bool] -> Bool
and              =  foldr (&&) True
or               =  foldr (||) False

skipMany1 :: Stream s m t => ParsecT s u m a -> ParsecT s u m ()
skipMany1 p applies the parser p one or more times, skipping its result.

sepBy :: Stream s m t => ParsecT s u m a -> ParsecT s u m sep -> ParsecT s u m [a]
sepBy p sep parses zero or more occurrences of p, separated by sep. Returns a list of values returned by p.

endBy :: Stream s m t => ParsecT s u m a -> ParsecT s u m sep -> ParsecT s u m [a]
endBy p sep parses zero or more occurrences of p, seperated and ended by sep. Returns a list of values returned by p.

letter :: Stream s m Char => ParsecT s u m Char
Parses a letter (an upper case or lower case character). Returns the parsed character.

digit :: Stream s m Char => ParsecT s u m Char
Parses a digit. Returns the parsed character.

char :: Stream s m Char => Char -> ParsecT s u m Char
char c parses a single character c. Returns the parsed character (i.e. c).

oneOf :: Stream s m Char => [Char] -> ParsecT s u m Char
oneOf cs succeeds if the current character is in the supplied list of characters cs. Returns the parsed character.

noneOf :: Stream s m Char => [Char] -> ParsecT s u m Char
As the dual of oneOf, noneOf cs succeeds if the current character not in the supplied list of characters cs

parse :: Stream s Identity t => Parsec s () a -> SourceName -> s -> Either ParseError a

reads            :: (Read a) => ReadS a
reads            =  readsPrec 0
-}
