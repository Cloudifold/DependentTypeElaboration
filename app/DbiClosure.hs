 {-# language LambdaCase, DerivingVia, Strict #-}

module DbiClosure where

import Prelude hiding (length, lookup)
import Control.Applicative hiding (many, some)
import Data.Char
import Data.Void
import System.Environment
import System.Exit

-- De Bruijin Index
newtype Ix = Ix Int
    deriving (Eq, Show, Num) via Int

-- De Brujin Level
newtype Lvl = Lvl Int
    deriving (Eq, Show, Num) via Int

data Term
    = Var Ix
    | Lam Term
    | App Term Term
    | Let Term Term
    deriving (Show)


data Ctxt
    = Nil
    | Cons Ctxt ~Val

data Closure
    = Closure Ctxt Term

data Val
    = VVar Lvl
    | VApp Val ~Val
    | VLam Closure

length :: Ctxt -> Lvl
length = f 0 where
    f n Nil = n
    f n (Cons ctxt _) = f (n + 1) ctxt

lookup :: Ctxt -> Ix -> Val
lookup (Cons ctxt v) 0 = v
lookup (Cons ctxt v) n = lookup ctxt (n - 1)
lookup _             _ = error "index out of scope"

cApp :: Closure -> Val -> Val
cApp (Closure ctxt t) ~v = eval (Cons ctxt v) t

eval :: Ctxt -> Term -> Val
eval ctxt = \case
    Var x   -> lookup ctxt x
    App t u -> case (eval ctxt t, eval ctxt u) of
                (VLam c, v2) -> cApp c  v2
                (v1    , v2) -> VApp v1 v2
    Lam t  -> VLam (Closure ctxt t)
    Let t u -> eval (Cons ctxt (eval ctxt t)) u

--   context length   level  index  
lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl n) (Lvl m) = Ix (n - m - 1)

quote :: Lvl -> Val -> Term
quote l = \case
    VVar x   -> Var (lvl2Ix l x)
    VApp t u -> App (quote l t) (quote l u)
    VLam c   -> Lam (quote (l + 1) (cApp c (VVar l)))

normalform :: Ctxt -> Term -> Term
normalform ctxt t = quote (length ctxt) (eval ctxt t)



