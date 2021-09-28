module Main where

import System.Environment
import ApplicativeParser
import DtTyCkDbi hiding (main)
import Main.Utf8 (withUtf8)
main = withUtf8 $ mainWith getArgs parseStdin
