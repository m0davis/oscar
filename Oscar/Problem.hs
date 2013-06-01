{-# LANGUAGE FlexibleContexts #-}
module Oscar.Problem where

import Text.Parsec
import Data.Char
import Data.String
import Data.Ratio
import Numeric

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

type Key = String
type JustificationType = Rational  

data 
    Premise
  = Premise
      Key
      Rational
  deriving Show

data
    Problem
  = Problem
      ProblemNumber
      ProblemDescription
      [Premise]
  deriving Show

problemParser :: Stream s m Char => ParsecT s u m Problem
problemParser 
  = do
    string "Problem #"
    n <- many1 digit
    newline
    s <- manyTill anyChar $ try newline
    string "Given premises:"
    newline
    many space
    k <- many1 alphaNum
    many space
    string "justification = "
    j <- manyTill anyChar $ try newline
    return (Problem (ProblemNumber (read n)) (ProblemDescription s) [Premise k (fst . head $ readFloat j)])

main :: IO ()
main = do
  putStrLn . show $ Problem (ProblemNumber 1) (ProblemDescription "hello world") [Premise "p1" 1]
  putStrLn . show $ Problem (ProblemNumber 2) (ProblemDescription "goodbye world") [Premise "p1" 1, Premise "p2" (1 % 2)]
  parseTest problemParser "Problem #1\nThis is a case of collective rebutting defeat\nGiven premises:\n     P    justification = 1.0\n     A    justification = 1.0\nUltimate epistemic interests:\n     R    interest = 1.0\n    FORWARDS PRIMA FACIE REASONS\n      pf-reason_1:   {P} ||=> Q   strength = 1.0\n      pf-reason_2:   {Q} ||=> R   strength = 1.0\n      pf-reason_3:   {C} ||=> ~R   strength = 1.0\n      pf-reason_4:   {B} ||=> C   strength = 1.0\n      pf-reason_5:   {A} ||=> B   strength = 1.0\n"
