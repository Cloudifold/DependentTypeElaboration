{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module DtTyCkNames where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf
import Text.Megaparsec.Error (errorBundlePretty)

type Name = String

type Ty = Term

type Raw = Term

data Term
  = Var Name
  | Lam Name Term
  | App Term Term
  | U
  | Pi Name Ty Ty
  | Let Name Ty Term Term
  | SrcPos SourcePos Term

{-
    Theory :

    ctxt , x : A |- , t(x) : B
    -----------------
    ctxt |- Lam x t : A -> B

    ctxt |- u : A , t : A -> B
    ----------------
    ctxt |- App t u : B

    ctxt , x : A |- t(x) : B    ctxt |- u : A
    ----------------
    ctxt |- App (Lam x t) u = t(u) : B

    ctxt , x : A |- B(x) : U
    ----------------
    ctxt |- Pi x A B : U

    ctxt , x : A |- t(x) : B(x)
    ----------------
    ctxt |- Lam x t(x) : Pi x A B

    ctxt |- t : Pi x A B , u : A
    ----------------
    ctxt |- App t u : B(u)

    ctxt , x : A |- t(x) : B(x)    ctxt |- u : A
    ----------------
    ctxt |- App (Lam x t) u = t(u) : B(u)

 -}

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Env = [(Name, Val)]

-- Not Telescope
-- Context of Term(Value)-level

fresh :: Env -> Name -> Name
fresh env "_" = "_"
fresh env x = case lookup x env of
  Just _ -> fresh env (x ++ "'")
  _ -> x

eval :: Env -> Term -> Val
eval env = \case
  Var x -> fromJust $ lookup x env
  App t u -> case (eval env t, eval env u) of
    (VLam _ t, u) -> t u -- eta-reduction using HOAS
    (t, u) -> VApp t u
  Lam x t -> VLam x (\u -> eval ((x, u) : env) t)
  Pi x a b -> VPi x (eval env a) (\u -> eval ((x, u) : env) b)
  Let x a t u -> eval ((x, eval env t) : env) u
  U -> VU
  SrcPos _ t -> eval env t

quote :: Env -> Val -> Term
quote env = \case
  VVar x -> Var x
  VApp t u -> App (quote env t) (quote env u)
  VLam x t ->
    let x' = fresh env x
      in Lam x' (quote ((x', VVar x') : env) (t (VVar x)))
  VPi x a b ->
    let x' = fresh env x
      in Pi x' (quote env a) (quote ((x, VVar x) : env) (b (VVar x)))
  VU -> U

normalform :: Env -> Term -> Term
normalform env = quote env . eval env

normalform0 :: Term -> Term
normalform0 = normalform []

-- | Beta-eta conversion checking
conv :: Env -> Val -> Val -> Bool
conv env t u = case (t, u) of
  (VU, VU) -> True
  (VPi x a b, VPi x' a' b') ->
    let y = fresh env x
        y' = fresh env x'
      in conv env a a' && conv ((y, VVar y) : env) (b (VVar y)) (b' (VVar y'))
  (VLam x t, VLam x' t') ->
    let y = fresh env x
        y' = fresh env x'
      in conv ((y, VVar y) : env) (t (VVar y)) (t' (VVar y'))
  -- eta conversion for Lam
  (VLam x t, u) ->
    let y = fresh env x
      in conv ((y, VVar y) : env) (t (VVar y)) (VApp u (VVar y))
  (u, VLam x t) ->
    let y = fresh env x
      in conv ((y, VVar y) : env) (VApp u (VVar y)) (t (VVar y))
  (VVar x, VVar x') -> x == x'
  (VApp t u, VApp t' u') -> conv env t t' && conv env u u'
  _ -> False

type VTy = Val

type Ctxt = [(Name, VTy)]

-- | Typechecking monad. After we throw an error, we annotate it at the innermost
--   point in the syntax where source position information is available from
--   a 'SrcPos' 'Tm' constructor.
type M = Either (String, Maybe SourcePos)

report :: String -> M a
report str = Left (str, Nothing)

qouteShow :: Env -> Val -> String
qouteShow env = show . quote env

addPos :: SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) -> Left (msg, Just pos)
  ma -> ma

check :: Env -> Ctxt -> Raw -> VTy -> M ()
--                      term  type
check env ctxt t a = case (t, a) of
  (SrcPos pos t, _) -> addPos pos (check env ctxt t a)
  (Lam x t, VPi x' a b) ->
    let y = fresh env x'
      in check ((x, VVar y) : env) ((x, a) : ctxt) t (b (VVar y))
  (Let x a' t' u, _) -> do
    check env ctxt a' VU -- is a' : U ?
    let ~a'' = eval env a' -- VTy
    check env ctxt t' a'' -- is t' : a' ?
    check ((x, eval env t') : env) ((x, a'') : ctxt) u a
  _ -> do
    tty <- infer env ctxt t
    unless (conv env tty a) $
      report
        ( printf
            "type mismatch\n\nexpected type:\n\n %s\n\ninferred type:\n\n %s\n"
            (qouteShow env a)
            (qouteShow env tty)
        )

infer :: Env -> Ctxt -> Raw -> M VTy
infer env ctxt = \case
  SrcPos pos t -> addPos pos (infer env ctxt t)
  Var x -> case lookup x ctxt of
    Nothing -> report $ "Name not in scope: " ++ x
    Just a -> pure a
  U -> pure VU
  App t u -> do
    tty <- infer env ctxt t
    case tty of
      VPi _ a b -> do
        check env ctxt u a
        pure (b (eval env u))
      tty ->
        report $
          "Expected a function type, instead inferred:\n\n"
            ++ qouteShow env tty
  Lam {} -> report "Can't infer type for lambda expresion"
  Pi x a b -> do
    check env ctxt a VU -- is a : U ?
    check ((x, VVar x) : env) ((x, eval env a) : ctxt) b VU -- is b(x) : U ?
    pure VU
  Let x a t u -> do
    check env ctxt a VU -- is a : U ?
    let ~a' = eval env a
    check env ctxt t a' -- is t : a' ?
    infer ((x, eval env t) : env) ((x, a') : ctxt) u -- infer u !

-- printing
atomp = 3 :: Int -- U, Var

appp = 2 :: Int -- App

pip = 1 :: Int -- Pi

letp = 0 :: Int -- Let, Lam

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTerm :: Int -> Term -> ShowS
prettyTerm prec = f prec
  where
    piBind x a =
      showParen True ((x ++) . (" : " ++) . f letp a)

    f :: Int -> Term -> ShowS
    f p = \case
      Var x -> (x ++)
      App t u -> par p appp $ f appp t . (' ' :) . f atomp u
      Lam x t -> par p letp $ ("λ " ++) . (x ++) . fLam t
        where
          fLam (Lam x t) = (' ' :) . (x ++) . fLam t
          fLam t = (". " ++) . f letp t
      U -> ("U" ++)
      Pi "_" a b -> par p pip $ f appp a . (" -> " ++) . f pip b
      Pi x a b -> par p pip $ piBind x a . fPi b
        where
          fPi (Pi x a b) | x /= "_" = piBind x a . fPi b
          fPi b = (" -> " ++) . f pip b
      Let x a t u ->
        par p letp $
          ("let " ++) . (x ++) . (" : " ++) . f letp a
            . ("\n    = " ++)
            . f letp t
            . ("\nin\n" ++)
            . f letp u
      SrcPos _ t -> f p t

instance Show Term where showsPrec = prettyTerm

-- --

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Term -> Parser Term
withPos p = SrcPos <$> getSourcePos <*> p

lexeme = L.lexeme ws

symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow  = symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "\\" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom =
        withPos ((Var <$> pIdent) <|> (U <$ symbol "U"))
    <|> parens pTerm

pBinder = pIdent <|> symbol "_"

pSpine = foldl1 App <$> some pAtom

pTerm = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)


pLam = do
  char '\\'
  xs <- some pBinder
  char '.'
  t <- pTerm
  pure (foldr Lam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pTerm)))
  pArrow
  cod <- pTerm
  pure $ foldr (\(xs, a) t -> foldr (`Pi` a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just a  -> Pi "_" sp <$> pTerm

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pTerm
  symbol "="
  t <- pTerm
  pKeyword "in"
  Let x a t <$> pTerm

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pSrc = ws *> pTerm <* eof

parseString :: String -> IO Term
parseString src = case parse pSrc "(stdin)" src of
  Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
  Right t -> pure t


parseStdin :: IO (Term, String)
parseStdin = do
  file <- getContents
  t <- parseString file
  pure (t, file)

-- main
---------

displayError :: String -> (String, Maybe SourcePos) -> IO ()
displayError file (msg, Just (SourcePos path (unPos -> linum) (unPos -> colnum))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
displayError _ _ = error "displayError: impossible: no available source position"

helpMsg =
  unlines
    [ "usage: Dt-Elab [--help|nf|type]",
      "  --help : display this message",
      "  nf     : read & typecheck expression from stdin, print its normal form and type",
      "  type   : read & typecheck expression from stdin, print its type"
    ]

mainWith :: IO [String] -> IO (Term, String) -> IO ()
mainWith getOpt getTerm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, file) <- getTerm
      putStrLn "Term : "
      print t
      case infer [] [] t of
        Left err -> displayError file err
        Right a -> do
          print $ normalform0 t
          putStrLn "  :"
          print $ quote [] a
    ["type"] -> do
      (t, file) <- getTerm
      putStrLn "Term : "
      print t
      either (displayError file) (print . quote []) $ infer [] [] t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)



