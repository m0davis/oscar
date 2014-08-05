{-# LANGUAGE NoImplicitPrelude #-}
module Main where

import ClassyPrelude

import Text.Show.Pretty                 (ppShow)

import Oscar.Problem                    (problemsM)

main :: IO ()
main = do
    problems <- problemsM $ fpFromString "combined-problems"
    putStrLn . pack . ppShow $ problems
