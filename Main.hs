{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Oscar.Main.Prelude

import Oscar.Main                       (combinedProblems)
import Oscar.Main                       (getBaseProblem)

import Oscar.ProblemParser              (readFileProblems)

main ∷ IO ()
main = do
    problems ← readFileProblems combinedProblems
    sequence_ $ putStrLn . pack . ppShow . getBaseProblem <$> problems
