{-# LANGUAGE NoImplicitPrelude #-}
module Main where

import ClassyPrelude

import Text.Show.Pretty                 (ppShow)

--import Oscar.Problem                    (testProblems)
import Oscar.Problem                    (ndProblemsM)

main :: IO ()
main = do
    --testProblems $ fpFromString "combined-problems"
    problems <- ndProblemsM $ fpFromString "combined-problems"
    putStrLn . pack . ppShow $ problems
