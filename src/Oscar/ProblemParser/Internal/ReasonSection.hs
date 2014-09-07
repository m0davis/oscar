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
     One of those sections, for example, starts with \"FORWARDS PRIMA FACIE REASONS\".
     Text within that section is first decoded into a ReasonSection and then
     finally into a 'ProblemForwardsPrimaFacieReason', a constituent of a
     'Oscar.Problem.Problem'.

     An instance of 'Oscar.ProblemParser.Internal.StatefullyParsed' constructs
     a 'ReasonSection'. Helper functions for this construction are provided
     below.

     Final decoding into constituents of a 'Oscar.Problem.Problem' is provided
     by 'FromReasonSection'.
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
    toForwardsReason,
    toBackwardsReason,
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

{- | This represents a partial deocde of one of the four kinds of
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

{- | Expects something like \"variables={A, B, ...}\" and returns the
     text between the curly braces (e.g. \"A, B, ...\").

     Consumes nothing and returns null text if it finds something unexpected.

     Leading whitespace and whitespace around the equal sign are acceptable.
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

{- | Expects something like \"some name or other:\" and returns the
     'ProblemReasonName' as the text prior to the colon.

     Leading whitespace is ignored. Consumes the colon.

     If no colon is found, the parser will fail without consuming anything.
-}
parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$>
    (try $
        many space *>
        manyTill anyChar (lookAhead . try $ char ':') <*
        char ':'
        )

{- | Expects something like \"{A, B, ...}\" and returns the comma-delimited
     items within (e.g. [\"A\", \" B\", \" ...\"]).

     Must start at the open curly-brace. Consumes everything up to and
     including the closing curly-brace.

     If the parser fails, nothing is consumed.
-}
parserEnbracedTexts ∷ Parser [Text]
parserEnbracedTexts = try $ do
    _ ← char '{'
    (inner, _) ← (pack <$> many anyChar) `precededBy` char '}'
    let texts = simpleParse (emptylist <|> p) inner
    return texts
  where
    emptylist ∷ Parser [Text]
    emptylist = try $ spaces >> eof >> return []

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
        (toForwardsReason $ _rsProblemReasonText r)
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
            (toForwardsReason $ _rsProblemReasonText r)

instance FromReasonSection ProblemBackwardsPrimaFacieReason
                           Backwards
                           PrimaFacie
  where
    fromReasonSection r = (,,)
        (_rsProblemReasonName r)
        (toBackwardsReason $ _rsProblemReasonText r)
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
            (toBackwardsReason $ _rsProblemReasonText r)

toForwardsReason 
    ∷ (Text ⁞ ƮReason Forwards defeasibility) 
      -- ^ a constituent of a 'ReasonSection'
    → ForwardsReason
toForwardsReason = simpleParse p . unƭ
  where
    p ∷ Parser ForwardsReason
    p = do
        (premiseTexts, _) ←
            parserEnbracedTexts
                `precededBy`
            (spaces >> string "||=>")
        spaces
        conclusionText ← pack <$> many anyChar
        return $ ForwardsReason
            (formulaFromText <$> premiseTexts)
            (formulaFromText conclusionText)

toBackwardsReason 
    ∷ (Text ⁞ ƮReason Backwards defeasibility)
      -- ^ a constituent of a 'ReasonSection'
    → BackwardsReason
toBackwardsReason = simpleParse p . unƭ
  where
    p ∷ Parser BackwardsReason
    p = do
        forwardsPremiseTextsText ←
            manyTill anyChar
                     (lookAhead . try $
                        many space *>
                        char '{' *>
                        many (notFollowedBy (char '}') *> anyChar) *>
                        char '}' *>
                        many space *>
                        string "||=>" *>
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
        return $ BackwardsReason
            (formulaFromText <$> forwardsPremiseTexts)
            (formulaFromText <$> backwardsPremiseTexts)
            (formulaFromText conclusionText)
