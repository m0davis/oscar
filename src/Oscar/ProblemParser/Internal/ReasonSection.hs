{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.ProblemParser.Internal.ReasonSection (
    ReasonSection,
    _rsProblemReasonName,
    _rsProblemReasonText,
    _rsProblemVariables,        
    _rsProblemStrengthDegree,
    parserProblemVariablesText,
    parserProblemReasonName,
    decodeReasonSection,            
    getForwardsReason,
    getBackwardsReason,
    parserEnbracedTexts,
    ) where

import Oscar.Main.Prelude
import Oscar.Main.Parser

import Oscar.ProblemParser.Internal.Tags    (Direction(Forwards))
import Oscar.ProblemParser.Internal.Tags    (Direction(Backwards))
import Oscar.ProblemParser.Internal.Tags    (Defeasibility)
import Oscar.ProblemParser.Internal.Tags    (ƮProblemVariables)
import Oscar.ProblemParser.Internal.Tags    (ƮReason)
import Oscar.ProblemParser.Internal.Tags    (ƮSection)
import Oscar.ProblemParser.Internal.Section    (runSectionParser)
import Oscar.ProblemParser.Internal.UnitIntervalParsers    (parserProblemStrengthDegree)

import Oscar.Problem                        (ProblemReasonName(ProblemReasonName))
import Oscar.Problem                        (ProblemStrengthDegree)
import Oscar.Problem                        (ForwardsReason(ForwardsReason))
import Oscar.Problem                        (BackwardsReason(BackwardsReason))
import Oscar.FormulaParser                  (formulaFromText)

-- | A partially-processed reason section
type ReasonSection (direction ∷ Direction) (defeasibility ∷ Defeasibility) =
    ( ProblemReasonName
    , Text ⁞ ƮReason direction defeasibility
    , Text ⁞ ƮProblemVariables
    , ProblemStrengthDegree
    )

_rsProblemReasonName ∷ ReasonSection direction defeasibility → ProblemReasonName
_rsProblemReasonName (n, _, _, _) = n

_rsProblemReasonText ∷ ReasonSection direction defeasibility → Text ⁞ ƮReason direction defeasibility
_rsProblemReasonText (_, t, _, _) = t

_rsProblemVariables ∷ ReasonSection direction defeasibility → Text ⁞ ƮProblemVariables
_rsProblemVariables (_, _, v, _) = v

_rsProblemStrengthDegree ∷ ReasonSection direction defeasibility → ProblemStrengthDegree
_rsProblemStrengthDegree (_, _, _, d) = d

parserProblemVariablesText ∷ Parser (Text ⁞ ƮProblemVariables)
parserProblemVariablesText = ƭ . pack <$> (option "" . try $ many space *> string "variables" *> many space *> char '=' *> many space *> char '{' *> manyTill anyChar (lookAhead . try $ char '}') <* char '}')

parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> (many space *> manyTill anyChar (lookAhead . try $ char ':') <* char ':')

-- | a helper for the various below decoders
decodeReasonSection ∷ Text ⁞ ƮSection (ƮReason direction defeasibility)
                    → [ReasonSection direction defeasibility]
decodeReasonSection = runSectionParser $ do
    n ← parserProblemReasonName
    spaces
    (t, (v, d)) ← many anyChar `precededBy` p'
    return $ (,,,) n (ƭ . (pack ∷ String → Text) $ t) v d
  where
    p' ∷ Parser (Text ⁞ ƮProblemVariables, ProblemStrengthDegree)
    p' = do
        t ← parserProblemVariablesText
        d ← parserProblemStrengthDegree
        return (t, d)

-- | A helper function
getForwardsReason ∷ Text ⁞ ƮReason Forwards defeasibility → ForwardsReason
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

-- | Another helper function
getBackwardsReason ∷ Text ⁞ ƮReason Backwards defeasibility → BackwardsReason
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
