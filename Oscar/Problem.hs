{-# LANGUAGE FlexibleContexts #-}
module Oscar.Problem where

import Text.Parsec
import Data.Char
import Data.String

newtype
    ProblemNumber
  = ProblemNumber
    Int
  deriving Show

newtype
    ProblemDescription
  = ProblemDescription
    String
  deriving Show

data
    Problem
  = Problem
    ProblemNumber
    ProblemDescription
  deriving Show

problemParser :: Stream s m Char => ParsecT s u m Problem
problemParser 
  = do
    string "Problem #"
    n <- many1 digit
    newline
    s <- many anyChar
    return (Problem (ProblemNumber (read n)) (ProblemDescription s))

main :: IO ()
main = do
  putStrLn . show $ Problem (ProblemNumber 1) (ProblemDescription "hello world")
  putStrLn . show $ Problem (ProblemNumber 2) (ProblemDescription "goodbye world")
  parseTest problemParser "Problem #42\nHello, World!"
