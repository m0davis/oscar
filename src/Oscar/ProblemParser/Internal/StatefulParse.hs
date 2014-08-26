{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.StatefulParse (
    StatefulParser(..),
    runStatefulParser,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem                        (ProblemNumber(ProblemNumber))
import Oscar.Problem                        (ProblemDescription(ProblemDescription))
import Oscar.ProblemParser.Internal.Tags    (ƮProblemAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemAfterNumber)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemAfterDescription)
import Oscar.ProblemParser.Internal.Section (sectionParser)

class StatefulParser a inState outState where
    statefulParser ∷ Parser a ⁞ (inState, outState)

-- | Uses 'simpleParse'.
runStatefulParser ∷ ∀ a inState outState.
    (StatefulParser a inState outState) ⇒ Text ⁞ inState → (a, Text ⁞ outState)
runStatefulParser = simpleParse p' . unƭ
  where
    p' ∷ Parser (a, Text ⁞ outState)
    p' = do
        v ← unƭ (statefulParser ∷ Parser a ⁞ (inState, outState))
        r ← pack <$> many anyChar
        return (v, ƭ r)

{- | ƮProblemAfterNumberLabel = after the "Problem #"

Sample Input

@
\"1 \\n Description\\n...etc...\\n"
@

Sample Output

@
(1, \" \\n Description\\n...etc...\\n")
@
-}
instance StatefulParser ProblemNumber ƮProblemAfterNumberLabel ƮProblemAfterNumber where
    statefulParser = ƭ $ ProblemNumber . read <$>
        manyTill anyChar (lookAhead . try $ space)

{- | ƮProblemAfterNumber = immediately after the integer after "Problem #".

Sample Input

@

Description

Given premises:
...etc...
@

Sample Output

@
("Description", "Given premises:\\n...etc...\\n")
@
-}
instance StatefulParser ProblemDescription ƮProblemAfterNumber ƮProblemAfterDescription where
    statefulParser = ƭ $ spaces >> ProblemDescription . pack <$>
        (try emptyDescription <|> filledDescription)
      where
        emptyDescription = do
            manyTill space (lookAhead . try $ sectionParser >> manyTill space newline)
        filledDescription = do
            manyTill anyChar $ lookAhead . try $ manyTill space newline >> spaces >> sectionParser  >> manyTill space newline
