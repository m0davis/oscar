{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A 'ReasonSection' represents a partial decode of one of the four kinds
     of sections (described in "Oscar.Documentation") pertaining to reasons.
     One of those sections, for example, starts with
     \"FORWARDS PRIMA FACIE REASONS\".

     This module provides for a partial decode of each of those sections.
-}

module Oscar.ProblemParser.Internal.ReasonSection (
    -- * decoding a 'ReasonSection'
    ReasonSection,
    _rsProblemReasonName,
    _rsProblemReasonText,
    _rsProblemVariables,
    _rsProblemStrengthDegree,
    -- fromReasonSection,
    -- * helpers
    parserProblemVariablesText,
    parserProblemReasonName,
    parserEnbracedTexts,
    -- * further decoding of parts of a 'ReasonSection'
    getForwardsReason,
    getBackwardsReason,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.FormulaParser                  (formulaFromText)
import Oscar.Problem                        (BackwardsReason(BackwardsReason))
import Oscar.Problem                        (ForwardsReason(ForwardsReason))
import Oscar.Problem                        (ProblemReasonName(ProblemReasonName))
import Oscar.Problem                        (ProblemStrengthDegree)
import Oscar.ProblemParser.Internal.Tags    (Defeasibility)
import Oscar.ProblemParser.Internal.Tags    (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags    (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags    (ƮReason)
import Oscar.ProblemParser.Internal.Tags    (ƮVariables)

{- | This represents a partial parse of one of the four kinds of
     reason sections.
-}
type ReasonSection (direction ∷ Direction) (defeasibility ∷ Defeasibility) =
    ( ProblemReasonName
    , Text ⁞ ƮReason direction defeasibility
    , Text ⁞ ƮVariables
    , ProblemStrengthDegree
    )

_rsProblemReasonName ∷ ReasonSection direction defeasibility → ProblemReasonName
_rsProblemReasonName (n, _, _, _) = n

_rsProblemReasonText ∷ ReasonSection direction defeasibility → Text ⁞ ƮReason direction defeasibility
_rsProblemReasonText (_, t, _, _) = t

_rsProblemVariables ∷ ReasonSection direction defeasibility → Text ⁞ ƮVariables
_rsProblemVariables (_, _, v, _) = v

_rsProblemStrengthDegree ∷ ReasonSection direction defeasibility → ProblemStrengthDegree
_rsProblemStrengthDegree (_, _, _, d) = d

{- | Expects something like \"variables = {A,B,...}\". Accepts preceding
     whitespace. Resultant parse is that between the curly braces (e.g.
     \"A,B,...\").
-}
parserProblemVariablesText ∷ Parser (Text ⁞ ƮVariables)
parserProblemVariablesText = ƭ . pack <$> (option "" . try $ many space *> string "variables" *> many space *> char '=' *> many space *> char '{' *> manyTill anyChar (lookAhead . try $ char '}') <* char '}')

parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> (many space *> manyTill anyChar (lookAhead . try $ char ':') <* char ':')

{- | Expects to start at the beginning of the curly braces. Parses each of
     the comma-delimited items within.
-}
parserEnbracedTexts ∷ Parser [Text]
parserEnbracedTexts = do
    _ ← char '{'
    (inner, _) ← (pack <$> many anyChar) `precededBy` char '}'
    let texts = simpleParse (try emptylist <|> p) inner
    return texts
  where
    emptylist ∷ Parser [Text]
    emptylist = spaces >> eof >> return []

    p ∷ Parser [Text]
    p = do
        (firstText, restText) ←
            (many space *> (pack <$> manyTill anyChar (try $ lookAhead (many space >> eof))) <* many space)
                `precededBy`
            (lookAhead $ (try (many space >> eof) *> pure False) <|> try (char ',' *> many anyChar *> pure True))
        if restText then do
            _ ← char ','
            spaces -- TODO: remove if unnecessary
            restTexts ← p
            return $ firstText : restTexts
        else do
            return [firstText]

getForwardsReason ∷ (Text ⁞ ƮReason Forwards defeasibility)  -- ^ possibly as obtained from 'TODO fromReasonSection'
                  → ForwardsReason
getForwardsReason = uncurry ForwardsReason . booyah . unƭ . extractFromProblemReasonTextForwards
  where
    booyah = first (map formulaFromText) . second formulaFromText

    -- | Needs refactoring?
    extractFromProblemReasonTextForwards ∷
        Text ⁞ ƮReason Forwards defeasibility →
        ([Text], Text) ⁞ ƮReason Forwards defeasibility
    extractFromProblemReasonTextForwards = ƭ . simpleParse p . unƭ
      where
        p ∷ Parser ([Text], Text)
        p = do
            (premiseTexts, _) ← parserEnbracedTexts `precededBy` (many space >> string "||=>" >> many space)
            conclusionText ← pack <$> many anyChar
            return (premiseTexts, conclusionText)

getBackwardsReason ∷ (Text ⁞ ƮReason Backwards defeasibility)  -- ^ possibly as obtained from 'TODO fromReasonSection'
                   → BackwardsReason
getBackwardsReason = booyah . unƭ . extractFromProblemReasonTextBackwards
  where
    booyah (fps, bps, c) = BackwardsReason (formulaFromText <$> fps) (formulaFromText <$> bps) (formulaFromText c)

    extractFromProblemReasonTextBackwards ∷
        Text ⁞ ƮReason Backwards defeasibility →
        ([Text], [Text], Text) ⁞ ƮReason Backwards defeasibility
    extractFromProblemReasonTextBackwards = ƭ . simpleParse p . unƭ
      where
        p ∷ Parser ([Text], [Text], Text)
        p = do
            forwardsPremiseTextsText ← manyTill anyChar (lookAhead . try $ (many space >> char '{' >> many (notFollowedBy (char '}') >> anyChar) >> char '}' >> many space >> string "||=>" >> many space))
            forwardsPremiseTexts ← withInput (pack forwardsPremiseTextsText) parserEnbracedTexts
            spaces
            (backwardsPremiseTexts, _) ← parserEnbracedTexts `precededBy` (many space >> string "||=>" >> many space)
            conclusionText ← pack <$> many anyChar
            return (forwardsPremiseTexts, backwardsPremiseTexts, conclusionText)
