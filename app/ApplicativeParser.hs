module ApplicativeParser where

import Data.Char
import Prelude hiding (fmap)

newtype Parser a = P {unP :: String -> [(String, a)]}

pmap :: (a -> b) -> Parser a -> Parser b
pmap f (P g) = P (map (\(s,a) -> (s, f a)) . g)

-- | Operator version of 'pmap'.
(<#>) :: (a -> b) -> Parser a -> Parser b
(<#>) = pmap

-- | Parse a value and replace it.
(<#) :: a -> Parser b -> Parser a
(<#) a = pmap (const a)

infixl 4 <#>

infixl 4 <#

-- | Parse a character only when a predicate matches.
predP :: (Char -> Bool) -> Parser Char
predP p = P (\ s -> case s of
  [] -> []
  (c : str) -> [(str,c) | p c])

-- | Succeed only when parsing the given character.
charP :: Char -> Parser Char
charP c = P (\ s -> case s of
  [] -> []
  (c' : str) -> [(str,c) | c == c'])

-- | Inject a value into an identity parser.
inject :: a -> Parser a
inject x = P (\s -> [(s,x)])

-- | Given a parser with a function value and another parser, parse the function
-- first and then the value, return a parser which applies the function to the
-- value.

(<@>) :: Parser (a -> b) -> Parser a -> Parser b
(<@>) (P f) (P g) = P (\s -> q (f s) g )
  where
    q :: [(String, a -> b)] -> (String -> [(String, a)]) -> [(String, b)]
    q [] f = []
    q ((s, fab) : xs) f = map (\(s, a) -> (s, fab a)) (f s) ++ q xs f


(<@) :: Parser a -> Parser b -> Parser a
pa <@ pb = pmap const pa <@> pb

(@>) :: Parser a -> Parser b -> Parser b
pa @> pb = (id <# pa) <@> pb

infixl 4 <@

infixl 4 @>

infixl 4 <@>



-- | Parse a whole string.
stringP :: String -> Parser String
stringP ss = foldl ((<@>) . pmap (\s x -> s ++ [x])) (inject []) (map charP ss)


-- | Construct a parser that never parses anything.
emptyP :: Parser a
emptyP = P (const [])

-- | Combine two parsers: When given an input, provide the results of both parser run on the input.
(<<>>) :: Parser a -> Parser a -> Parser a
(<<>>) pf pg = P (\ss -> unP pf ss ++ unP pg ss)

infixl 3 <<>>

-- | Apply the parser zero or more times.
many :: Parser a -> Parser [a]
many p = inject [] <<>> some p

-- | Apply the parser one or more times.
some :: Parser a -> Parser [a]
some p = pmap (:) p <@> many p
-- | Apply a parser and return all ambiguous results, but only those where the input was fully consumed.
runParser :: Parser a -> String -> [a]
runParser (P f) cs = map snd (f cs)

-- | Apply a parser and only return a result, if there was only one unambiguous result with output fully consumed.
runParserUnique :: Parser a -> String -> Maybe a
runParserUnique p cs = case unP p cs of
  [([],x)] -> Just x
  _ -> Nothing


-- | Kinds of binary operators.
data BinOp = AddBO | MulBO deriving (Eq, Show)

-- | Some kind of arithmetic expression.
data Expr
  = ConstE Int
  | BinOpE BinOp Expr Expr
  | NegE Expr
  | ZeroE
  deriving (Eq, Show)

evalExpr :: Expr -> Int
evalExpr (ConstE n) = n
evalExpr (BinOpE AddBO ex ex') = evalExpr ex + evalExpr ex'
evalExpr (BinOpE MulBO ex ex') = evalExpr ex * evalExpr ex'
evalExpr (NegE ex) = - evalExpr ex
evalExpr ZeroE = 0

-- | Parse arithmetic expressions, with the following grammar:
--
--     expr         ::= const | binOpExpr | neg | zero
--     const        ::= int
--     binOpExpr    ::= '(' expr ' ' binOp ' ' expr ')'
--     binOp        ::= '+' | '*'
--     neg          ::= '-' expr
--     zero         ::= 'z'
parseExpr :: String -> Maybe Expr
parseExpr = runParserUnique exprP 


digitP :: Parser Char
digitP = foldr ((<<>>) . charP) (charP '0') "123456789"

strToInt :: [Char] -> Int
strToInt = foldl (\x c -> digitToInt c + (10 * x)) 0

constP :: Parser Expr
constP = ConstE <#> (strToInt <#> some digitP)

zeroP :: Parser Expr
zeroP = pmap q (stringP "z")
  where
    q :: String -> Expr
    q ['z'] = ZeroE
    q _     = error "Not 'z'"

negP :: Parser Expr -> Parser Expr
negP p = NegE <#> (charP '-' @> p)  

addP :: Parser Expr -> Parser Expr
addP p = BinOpE AddBO <#> (charP '(' @> p <@ stringP " + ") <@> (p <@ charP ')')

mulP :: Parser Expr -> Parser Expr
mulP p = BinOpE MulBO <#> (charP '(' @> p <@ stringP " * ") <@> (p <@ charP ')')

exprP :: Parser Expr
exprP = zeroP <<>> constP <<>> negP exprP <<>> mulP exprP <<>> addP exprP

