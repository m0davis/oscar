{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A 'ReasonSection' represents a partial decode of one of the four kinds
     of sections (described in "Oscar.Documentation") pertaining to reasons.
     One of those sections, for example, starts with
     \"FORWARDS PRIMA FACIE REASONS\".

     This module provides for a partial decode of each of those sections into
     'ReasonSection's as well as a final full decode of those 'ReasonSection's
     into constituents of a 'Oscar.Problem.Problem'.
-}

module Oscar.ProblemParser.Internal.ReasonSection (
    -- * 'ReasonSection'
    ReasonSection,
    _rsProblemReasonName,
    _rsProblemReasonText,
    _rsProblemVariables,
    _rsProblemStrengthDegree,
    -- ** construction helpers
    parserProblemVariablesText,
    parserProblemReasonName,
    parserEnbracedTexts,
    -- * decoding a 'ReasonSection'
    FromReasonSection(..),
    -- ** decoding helpers 
    getForwardsReason,
    getBackwardsReason,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.FormulaParser                  (formulaFromText)
import Oscar.Problem                        (BackwardsReason(BackwardsReason))
import Oscar.Problem                        (ForwardsReason(ForwardsReason))
import Oscar.Problem                        (LispPositiveDouble(LispPositiveDouble))
import Oscar.Problem                        (ProblemBackwardsConclusiveReason)
import Oscar.Problem                        (ProblemBackwardsPrimaFacieReason)
import Oscar.Problem                        (ProblemForwardsConclusiveReason)
import Oscar.Problem                        (ProblemForwardsPrimaFacieReason)
import Oscar.Problem                        (ProblemReasonName(ProblemReasonName))
import Oscar.Problem                        (ProblemStrengthDegree(ProblemStrengthDegree))
import Oscar.ProblemParser.Internal.Tags    (Defeasibility(Conclusive))
import Oscar.ProblemParser.Internal.Tags    (Defeasibility(PrimaFacie))
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

_rsProblemReasonName 
    ∷ ReasonSection direction defeasibility 
    → ProblemReasonName
_rsProblemReasonName (n, _, _, _) = n

_rsProblemReasonText 
    ∷ ReasonSection direction defeasibility 
    → Text ⁞ ƮReason direction defeasibility
_rsProblemReasonText (_, t, _, _) = t

_rsProblemVariables 
    ∷ ReasonSection direction defeasibility 
    → Text ⁞ ƮVariables
_rsProblemVariables (_, _, v, _) = v

_rsProblemStrengthDegree 
    ∷ ReasonSection direction defeasibility 
    → ProblemStrengthDegree
_rsProblemStrengthDegree (_, _, _, d) = d

{- | Expects something like \"variables = {A,B,...}\". Accepts preceding
     whitespace. Resultant parse is that between the curly braces (e.g.
     \"A,B,...\").
-}
parserProblemVariablesText ∷ Parser (Text ⁞ ƮVariables)
parserProblemVariablesText = ƭ . pack <$> 
    (option "" . try $ 
        many space *> 
        string "variables" *> 
        many space *> 
        char '=' *> 
        many space *> 
        char '{' *> 
        manyTill anyChar (lookAhead . try $ char '}') <* 
        char '}'
        )

parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> 
    (many space *> 
     manyTill anyChar (lookAhead . try $ char ':') <* 
     char ':'
     )

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
            (many space *> 
                (pack <$> manyTill anyChar (try $ lookAhead (many space >> eof))) <* 
                many space
                )
                `precededBy`
            (lookAhead $ 
                (try (many space >> eof) *> pure False) 
                    <|> 
                try (char ',' *> many anyChar *> pure True)
                )
        if restText then do
            _ ← char ','
            spaces -- TODO: remove if unnecessary
            restTexts ← p
            return $ firstText : restTexts
        else do
            return [firstText]

{- | Defines types that can be constructed from a 'ReasonSection'. -}
class FromReasonSection to fromDirection fromDefeasibility where
    fromReasonSection ∷ ReasonSection fromDirection fromDefeasibility → to

instance FromReasonSection ProblemForwardsPrimaFacieReason 
                           Forwards 
                           PrimaFacie 
  where
    fromReasonSection r = (,,)
        (_rsProblemReasonName r)
        (getForwardsReason $ _rsProblemReasonText r)
        (_rsProblemStrengthDegree r)

instance FromReasonSection ProblemForwardsConclusiveReason 
                           Forwards 
                           Conclusive 
  where
    fromReasonSection r = case _rsProblemStrengthDegree r of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName r)
            (getForwardsReason $ _rsProblemReasonText r)

instance FromReasonSection ProblemBackwardsPrimaFacieReason 
                           Backwards 
                           PrimaFacie 
  where
    fromReasonSection r = (,,)
        (_rsProblemReasonName r)
        (getBackwardsReason $ _rsProblemReasonText r)
        (_rsProblemStrengthDegree r)

instance FromReasonSection ProblemBackwardsConclusiveReason 
                           Backwards 
                           Conclusive 
  where
    fromReasonSection r = case (_rsProblemStrengthDegree r) of
        ProblemStrengthDegree (LispPositiveDouble 1) → result
        _ → error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName r)
            (getBackwardsReason $ _rsProblemReasonText r)

getForwardsReason ∷ (Text ⁞ ƮReason Forwards defeasibility)  -- ^ possibly as obtained from 'TODO fromReasonSection'
                  → ForwardsReason
getForwardsReason = id
    . uncurry ForwardsReason
    . booyah
    . unƭ
    . extractFromProblemReasonTextForwards
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
            (premiseTexts, _) ← 
                parserEnbracedTexts 
                    `precededBy` 
                (many space >> string "||=>" >> many space)
            conclusionText ← pack <$> many anyChar
            return (premiseTexts, conclusionText)

getBackwardsReason ∷ (Text ⁞ ƮReason Backwards defeasibility)  -- ^ possibly as obtained from 'TODO fromReasonSection'
                   → BackwardsReason
getBackwardsReason = booyah . unƭ . extractFromProblemReasonTextBackwards
  where
    booyah (fps, bps, c) = 
        BackwardsReason 
            (formulaFromText <$> fps) 
            (formulaFromText <$> bps) 
            (formulaFromText c)

    extractFromProblemReasonTextBackwards 
        ∷ Text ⁞ ƮReason Backwards defeasibility 
        → ([Text], [Text], Text) ⁞ ƮReason Backwards defeasibility
    extractFromProblemReasonTextBackwards = ƭ . simpleParse p . unƭ
      where
        p ∷ Parser ([Text], [Text], Text)
        p = do
            forwardsPremiseTextsText ← 
                manyTill anyChar 
                         (lookAhead . try $ 
                            many space >> 
                            char '{' >> 
                            many (notFollowedBy (char '}') >> anyChar) >> 
                            char '}' >> 
                            many space >> 
                            string "||=>" >> 
                            many space
                            )
            forwardsPremiseTexts ← 
                withInput (pack forwardsPremiseTextsText) parserEnbracedTexts
            spaces
            (backwardsPremiseTexts, _) ← 
                parserEnbracedTexts 
                    `precededBy` 
                (many space >> string "||=>" >> many space)
            conclusionText ← pack <$> many anyChar
            return 
                (forwardsPremiseTexts
                ,backwardsPremiseTexts
                ,conclusionText
                )
