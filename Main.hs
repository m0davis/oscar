{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import ClassyPrelude

import Data.Tagged                      (Tagged(Tagged))
import Text.Show.Pretty                 (ppShow)

import Oscar.Problem                    (problemsM)
import Oscar.Problem                    (extractFromProblemReasonTextForwards)
import Oscar.Problem                    (extractFromProblemReasonTextBackwards)
import Oscar.Problem                    (enbracedListParser)
import Oscar.Problem                    (ProblemReasonText(ProblemReasonText))
import Oscar.Problem                    (Direction(Backwards))
import Oscar.Problem                    (Defeasibility(Conclusive))
import Oscar.Problem                    (Problems)
import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  ((:::))

combinedProblems :: FilePath ::: Problems
combinedProblems = Tagged $ fpFromString "combined-problems"

--
testR :: ProblemReasonText Backwards Conclusive
testR = ProblemReasonText $ pack "{P} {(Q1 & Q2) , ~(Q1 & (Q2 & Q3))} ||=> ~Q3"

main :: IO ()
main = do
    --print $ simpleParse enbracedListParser (pack "{P v Q}")
    --print $ simpleParse enbracedListParser (pack "{}")
    ----print $ simpleParse enbracedListParser (pack "{P v Q}")
    ----print $ simpleParse enbracedListParser (pack "{Q1 & Q2, ~(Q1 & (Q2 & Q3))}")
    --print $ extractFromProblemReasonTextBackwards testR
    
    problems <- problemsM combinedProblems
    sequence_ $ putStrLn . pack . ppShow <$> problems
