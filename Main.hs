{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Oscar.Main.Prelude

import Oscar.Main                       (combinedProblems)
import Oscar.Main                       (getBaseProblem)
import Oscar.Main                       (testProblemFromProblemParser)

import Oscar.Problem                    (Problem)
import Oscar.ProblemParser              (readFileProblems)
import Oscar.ProblemParser              (stripLineComments)
import Oscar.ProblemParser.Internal     (partitionProblemsText)
import Oscar.ProblemParser.Internal     (problemFromText)

main ∷ IO ()
main = do
    let slc = stripLineComments $ testProblemFromProblemParser
    putStrLn . pack . ppShow $ slc

    let problems' :: [Problem] = map problemFromText . partitionProblemsText . stripLineComments $ testProblemFromProblemParser
    sequence_ $ putStrLn . pack . ppShow <$> problems'

    problems ← readFileProblems combinedProblems
    sequence_ $ putStrLn . pack . ppShow . getBaseProblem <$> problems
