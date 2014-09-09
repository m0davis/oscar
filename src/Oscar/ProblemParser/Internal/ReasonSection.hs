{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
--{-# LANGUAGE TemplateHaskell #-} -- TODO commented-out until we figure out
                                   -- how to make lenses for ReasonSection
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
    ReasonSection(..),
    -- ** construction helpers
    parserProblemVariablesText,
    parserProblemReasonName,
    parserEnbracedTexts,
    -- * decoding a 'ReasonSection'
    FromReasonSection(..),
    -- ** decoding helpers
    toForwardsReason,
    toBackwardsReason,
    ---- * "Control.Lens"
    --rsProblemReasonName,
    --rsProblemReasonText,
    --rsProblemVariables,
    --rsProblemStrengthDegree,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

--import Control.Lens

import Oscar.FormulaParser                  (formulaFromText)
import Oscar.Problem                        (BackwardsReason(BackwardsReason))
import Oscar.Problem                        (ForwardsReason(ForwardsReason))
import Oscar.Problem                        (Degree(Degree))
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
data ReasonSection (direction ∷ Direction) (defeasibility ∷ Defeasibility) =
    ReasonSection 
        { _rsProblemReasonName ∷ ProblemReasonName
        , _rsProblemReasonText ∷ (Text ⁞ ƮReason direction defeasibility)
        , _rsProblemVariables ∷ (Text ⁞ ƮVariables)
        , _rsProblemStrengthDegree ∷ ProblemStrengthDegree
        }

{- | Expects something like \"variables={A, B, ...}\" and returns the
     text between the curly braces (e.g. \"A, B, ...\").

     Consumes nothing and returns null text if it finds something unexpected.

     Leading whitespace and whitespace around the equal sign are acceptable.
-}
parserProblemVariablesText ∷ Parser (Text ⁞ ƮVariables)
parserProblemVariablesText = ƭ . pack <$>
    (option "" . try $
        spaces *>
        string "variables" *>
        spaces *>
        char '=' *>
        spaces *>
        char '{' *>
        manyTillBefore anyChar (char '}') <*
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
        spaces *>
        manyTillBefore anyChar (char ':') <*
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
    let texts = simpleParse (emptyList <|> nonEmptyList) inner
    return texts
  where
    emptyList ∷ Parser [Text]
    emptyList = spacesUpToEof *> return []

    nonEmptyList ∷ Parser [Text]
    nonEmptyList = do
        (firstText, restExists) ← 
            parserFirstText `precededBy` parserRestExists
        if restExists then do  -- there's an element after the first one
            _ ← char ','
            restTexts ← nonEmptyList
            return $ firstText : restTexts
        else do  -- this is the last element in the list
            return [firstText]
      where
        parserFirstText =
            (spaces *>
                (pack <$> manyTillBefore anyChar spacesUpToEof) <*
                spaces
                )

        parserRestExists = lookAhead $
            empty
            <|> spacesUpToEof *> pure False
            <|> try (char ',' *> pure True)

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
        ProblemStrengthDegree (Degree 1) → result
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
        ProblemStrengthDegree (Degree 1) → result
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
                        spaces *>
                        char '{' *>
                        many (notFollowedBy (char '}') *> anyChar) *>
                        char '}' *>
                        spaces *>
                        string "||=>" *>
                        spaces
                        )
        forwardsPremiseTexts ←
            withInput (pack forwardsPremiseTextsText) parserEnbracedTexts
        spaces
        (backwardsPremiseTexts, _) ←
            parserEnbracedTexts
                `precededBy`
            (spaces >> string "||=>" >> spaces)
        conclusionText ← pack <$> many anyChar
        return $ BackwardsReason
            (formulaFromText <$> forwardsPremiseTexts)
            (formulaFromText <$> backwardsPremiseTexts)
            (formulaFromText conclusionText)

-- TODO This doesn't work! Apparently, there's a problem with handling ⁞.
--makeLenses ''ReasonSection
