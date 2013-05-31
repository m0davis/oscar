module Oscar.Problem where

newtype ProblemNumber = ProblemNumber Int
newtype ProblemDescription = ProblemDescription String

data Problem = Problem 
  ProblemNumber 
  ProblemDescription

