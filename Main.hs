{-# LANGUAGE NoImplicitPrelude #-}
module Main where

import ClassyPrelude

import Text.Show.Pretty                 (ppShow)

import Oscar.Problem                    (ndProblemsM)

main :: IO ()
main = do
    problems <- ndProblemsM $ fpFromString "combined-problems"
    putStrLn . pack . ppShow $ problems
