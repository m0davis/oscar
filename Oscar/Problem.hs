module Oscar.Problem where

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

main :: IO ()
main = do
  putStrLn . show $ Problem (ProblemNumber 1) (ProblemDescription "hello world")
  putStrLn . show $ Problem (ProblemNumber 2) (ProblemDescription "goodbye world")
