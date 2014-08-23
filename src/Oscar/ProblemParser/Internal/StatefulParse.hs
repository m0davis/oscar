{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.StatefulParse (
    runStatefulParse',
    parseProblemNumber,
    parseProblemDescription,    
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem                        (ProblemNumber(ProblemNumber))
import Oscar.Problem                        (ProblemDescription(ProblemDescription))
import Oscar.ProblemParser.Internal.Tags    (ƮProblemAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemAfterNumber)
import Oscar.ProblemParser.Internal.Section (sectionParser)

-- | The default implementation uses 'simpleParse'.
runStatefulParse' ∷ ∀ value state1 state2.
    Parser value ⁞ state1 →
    Text ⁞ state1 →
    (value, Text ⁞ state2)
runStatefulParse' statefulParser = simpleParse p' . unƭ
  where
    p' ∷ Parser (value, Text ⁞ state2)
    p' = do
        v ← unƭ statefulParser
        r ← pack <$> many anyChar
        return (v, ƭ r)

parseProblemNumber ∷ Parser ProblemNumber ⁞ ƮProblemAfterNumberLabel
parseProblemNumber = ƭ $ ProblemNumber . read <$>
    manyTill anyChar (lookAhead . try $ space)

parseProblemDescription ∷ Parser ProblemDescription ⁞ ƮProblemAfterNumber
parseProblemDescription = ƭ $ spaces >> ProblemDescription . pack <$> 
    (try emptyDescription <|> filledDescription)
  where
    emptyDescription = do 
        manyTill space (lookAhead . try $ sectionParser >> manyTill space newline)
    filledDescription = do 
        manyTill anyChar $ lookAhead . try $ manyTill space newline >> spaces >> sectionParser  >> manyTill space newline
