{-# LANGUAGE NoImplicitPrelude #-}
module Main where

import ClassyPrelude

import Oscar.Problem                    (testProblems)

main :: IO ()
main = do
    testProblems $ fpFromString "combined-problems"
