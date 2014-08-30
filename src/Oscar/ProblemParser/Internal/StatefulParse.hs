{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.StatefulParse (
    StatefulParser(..),
    runStatefulParser,
    runStatefulParser',
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.Problem                        (ProblemNumber(ProblemNumber))
import Oscar.Problem                        (ProblemDescription(ProblemDescription))
import Oscar.ProblemParser.Internal.Tags    (ƮAfterNumberLabel)
import Oscar.ProblemParser.Internal.Tags    (ƮAfterNumber)
import Oscar.ProblemParser.Internal.Tags    (ƮAfterDescription)
import Oscar.ProblemParser.Internal.Tags    (ƮWithoutLineComments)
import Oscar.ProblemParser.Internal.Tags    (ƮEof)
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

runStatefulParser' ∷ ∀ a inState.
    (StatefulParser a inState ƮEof) ⇒ Text ⁞ inState → a
runStatefulParser' = simpleParse p' . unƭ
  where
    p' ∷ Parser a
    p' = do
        v ← unƭ (statefulParser ∷ Parser a ⁞ (inState, ƮEof))
        eof
        return v

{- | ƮAfterNumberLabel = after the "Problem #"

Sample Input

@
\"1 \\n Description\\n...etc...\\n"
@

Sample Output

@
(1, \" \\n Description\\n...etc...\\n")
@
-}
instance StatefulParser ProblemNumber ƮAfterNumberLabel ƮAfterNumber where
    statefulParser = ƭ $ ProblemNumber . read <$>
        manyTill anyChar (lookAhead . try $ space)

{- | ƮAfterNumber = immediately after the integer after "Problem #".

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
instance StatefulParser ProblemDescription ƮAfterNumber ƮAfterDescription where
    statefulParser = ƭ $ spaces >> ProblemDescription . pack <$>
        (try emptyDescription <|> filledDescription)
      where
        emptyDescription = do
            manyTill space (lookAhead . try $ sectionParser >> manyTill space newline)
        filledDescription = do
            manyTill anyChar $ lookAhead . try $ manyTill space newline >> spaces >> sectionParser  >> manyTill space newline

{- | Separate the text of concatenated problems. Each resulant problem starts
     after the number label, \"Problem #". 'ƮAfterNumberLabel'

Sample input

@
Problem #1
Description of the first problem
Given premises:
     P    justification = 1.0
...etc...

Problem #2
Description of the second problem
...etc...
@

Sample outputs

@
1
Description of the first problem
Given premises:
     P    justification = 1.0
...etc...
@

@
2
Description of the second problem
...etc...
@
-}
instance StatefulParser [Text ⁞ ƮAfterNumberLabel] ƮWithoutLineComments ƮEof where
    statefulParser = ƭ . many $ do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP
      where
        endP ∷ Parser ()
        endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))
