 {-# language Strict, LambdaCase, ViewPatterns #-}

module EvalHOAS where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Function
import Data.Void
import System.Environment
import System.Exit
import FlatParse.Stateful

-- import qualified Text.Megaparsec.Char       as C
-- import qualified Text.Megaparsec.Char.Lexer as L

type Name = String

data Term
    = Var Name
    | Lam Name Term
    | App Term Term
    | Let Name Term Term
    --  Let x = y in z
    deriving (Show)

data Value
    = VVar Name
    | VApp Value ~Value
    | VLam Name (Value -> Value)  

instance Show Value where
    show = \case
        VVar x  ->  x
        VApp t u  -> "VApp " ++ show t ++ " " ++ show u
        VLam x f  -> "VLam " ++ x  ++ " ? " 

type Ctxt = [(Name, Value)]

fresh :: [Name] -> Name -> Name
fresh names "_" = "_"
fresh names x   = case x `elem` names of
    True  -> fresh names (x ++ "'")
    False -> x

infixl 2 $$
($$) :: Value -> Value -> Value
($$) (VLam _ t) ~u = t u
($$) t          ~u = VApp t u

eval :: Ctxt -> Term -> Value
eval ctxt = \case
    Var x     -> fromJust $ lookup x ctxt
    App t u   -> (eval ctxt t) $$ (eval ctxt u)
    Lam x t   -> VLam x (\u -> eval ((x, u):ctxt) t )
    Let x t u -> eval ((x, eval ctxt t):ctxt) u

quote :: [Name] -> Value -> Term
quote names = \case
    VVar x         -> Var x
    VApp t u ->  App (quote names t) (quote names u)
    VLam x f  -> let x' = fresh names x in 
        Lam x' (quote (x':names) (f (VVar x')))

normalform :: Ctxt -> Term -> Term
normalform ctxt = quote (map fst ctxt) . eval ctxt






