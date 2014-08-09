{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import ClassyPrelude

import Data.Tagged                      (Tagged(Tagged))
import Text.Show.Pretty                 (ppShow)

--import Oscar.Problem                    (enbracedListParser)
--import Oscar.Problem                    (extractFromProblemReasonTextBackwards)
--import Oscar.Problem                    (extractFromProblemReasonTextForwards)
--import Oscar.Utilities                  (simpleParse)
import Oscar.Problem                    (Defeasibility(Conclusive))
import Oscar.Problem                    (Direction(Backwards))
import Oscar.Problem                    (Problem)
import Oscar.Problem                    (problemsM)
import Oscar.Problem                    (ƮReason)
import Oscar.ProblemBase                (pattern BaseProblem)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (ƭ)

combinedProblems ∷ FilePath ⁞ [Problem]
combinedProblems = Tagged $ fpFromString "combined-problems"

--
testR :: Text ⁞ ƮReason Backwards Conclusive
testR = ƭ $ pack "{P} {(Q1 & Q2) , ~(Q1 & (Q2 & Q3))} ||=> ~Q3"

main ∷ IO ()
main = do
    --print $ simpleParse enbracedListParser (pack "{P v Q}")
    --print $ simpleParse enbracedListParser (pack "{}")
    ----print $ simpleParse enbracedListParser (pack "{P v Q}")
    ----print $ simpleParse enbracedListParser (pack "{Q1 & Q2, ~(Q1 & (Q2 & Q3))}")
    --print $ extractFromProblemReasonTextBackwards testR
    
    problems <- problemsM combinedProblems
    --sequence_ $ putStrLn . pack . ppShow <$> problems
    sequence_ $ putStrLn . pack . ppShow . bp <$> problems
  where
    --bp ∷ Problem -> BaseProblem 
    bp bp'@(BaseProblem _ _ _ _ _ _) = bp'
    bp _ = error "impossible? Problem does not match BaseProblem"
