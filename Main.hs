{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (
    main,
    ) where

import Oscar.Main.Prelude

import Oscar.Main                       (combinedProblemsPath)

import Oscar.ProblemParser              (readFileProblems)

import Oscar.Main.Test

{- | At the moment, the executable simply reads from a file called
     "combined-probems", parses the problems, and prints a structured
     representation.

    TODO implement the rest of Oscar
-}
main ∷ IO ()
main = do
    problems ← readFileProblems combinedProblemsPath
    sequence_ $ ppPrint <$> problems

    print $ foo 0
