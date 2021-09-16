{-# LANGUAGE Strict #-}

module ParserScratch where

newtype Parser a = P {unP :: String -> [(String, a)]}
