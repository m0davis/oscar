{-# LANGUAGE NoImplicitPrelude #-}
module Main where

import ClassyPrelude

import Text.Show.Pretty                 (ppShow)

import Oscar.Problem                    (problemsM)
import Oscar.Problem                    (extractFromProblemReasonTextForwards)
import Oscar.Problem                    (testR)
import Oscar.Problem                    (enbracedListParser)
import Oscar.Utilities                  (simpleParse)


main :: IO ()
main = do
    --print $ simpleParse enbracedListParser (pack "{P v Q}")
    --print $ simpleParse enbracedListParser (pack "{Q1 & Q2, ~(Q1 & (Q2 & Q3))}")
    --print $ extractFromProblemReasonTextForwards testR
    
    problems <- problemsM $ fpFromString "combined-problems"
    sequence_ $ putStrLn . pack . ppShow <$> problems
