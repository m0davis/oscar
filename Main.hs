{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import ClassyPrelude

import Data.Tagged                      (Tagged(Tagged))
import Text.Show.Pretty                 (ppShow)

import Oscar.Problem                    (problemsM)
--import Oscar.Problem                    (extractFromProblemReasonTextForwards)
--import Oscar.Problem                    (extractFromProblemReasonTextBackwards)
--import Oscar.Problem                    (enbracedListParser)
import Oscar.Problem                    (ƮReason)
import Oscar.Problem                    (Direction(Backwards))
import Oscar.Problem                    (Defeasibility(Conclusive))
import Oscar.Problem                    (ƮProblem)
--import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (ƭ)

combinedProblems :: FilePath ⁞ [ƮProblem]
combinedProblems = Tagged $ fpFromString "combined-problems"

--
testR :: Text ⁞ ƮReason Backwards Conclusive
testR = ƭ $ pack "{P} {(Q1 & Q2) , ~(Q1 & (Q2 & Q3))} ||=> ~Q3"

main :: IO ()
main = do
    --print $ simpleParse enbracedListParser (pack "{P v Q}")
    --print $ simpleParse enbracedListParser (pack "{}")
    ----print $ simpleParse enbracedListParser (pack "{P v Q}")
    ----print $ simpleParse enbracedListParser (pack "{Q1 & Q2, ~(Q1 & (Q2 & Q3))}")
    --print $ extractFromProblemReasonTextBackwards testR
    
    problems <- problemsM combinedProblems
    sequence_ $ putStrLn . pack . ppShow <$> problems
