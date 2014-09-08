{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (
    main,
    ) where

import Oscar.Main.Prelude

import Oscar.Main                       (combinedProblemsPath)

import Oscar.ProblemParser              (readFileProblems)

{- | At the moment, the executable simply reads from a file called
     "combined-probems", parses the problems, and prints a structured
     representation. Reading and parsing the file is done with 
     'readFileProblems'. The file itself is denoted by 'combinedProblemsPath'.
     Printing is done by 'ppPrint'.

     TODO implement the rest of Oscar
-}
main ∷ IO ()
main = do
    problems ← readFileProblems combinedProblemsPath
    sequence_ $ ppPrint <$> problems
