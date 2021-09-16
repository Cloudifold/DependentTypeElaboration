module Main where

import DbiClosure


t0 = (App (Lam (Var 0)) (Lam (Var 0)))

main = print (normalform  Nil t0) 

