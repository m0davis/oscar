{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Oscar.Main.Prelude

import Oscar.ProblemParser.Internal         (evalStatefulParser)
import Oscar.ProblemParser.Internal.Tags    (ƮWithoutLineComments)
import Oscar.ProblemParser.Internal.Tags    (ƮAfterNumberLabel)

import Text.Heredoc

testText ∷ Text ⁞ ƮWithoutLineComments
testText = ƭ . pack $ 
    [str|Problem #1
        |Description of the first problem
        |Given premises:
        |     P    justification = 1.0
        |...etc...
        |
        |Problem #2
        |Description of the second problem
        |...etc...
        |]

main ∷ IO ()
main = do
    ppPrint . unƭ $ testText
    ppPrint . map unƭ $ (evalStatefulParser testText :: [Text ⁞ ƮAfterNumberLabel])

    putStrLn . unƭ $ testText
    sequence_ $ map putStrLn . map unƭ $ (evalStatefulParser testText :: [Text ⁞ ƮAfterNumberLabel])
