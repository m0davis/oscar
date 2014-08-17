{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.Problem (
    -- * highest-level
        problemsM,
        Problem(..),
    -- * API
        readProblemsTextFile,
        partitionProblemsText,
        problemFromText,
    -- * misc. picky stuff
        _rbProblemReasonName,
        _rbProblemReasonText,
        _rbProblemStrengthDegree,
    -- * section decoders
        decodeForwardsPrimaFacieReasonSection,
        decodeForwardsConclusiveReasonSection,
        decodeBackwardsPrimaFacieReasonSection,
        decodeBackwardsConclusiveReasonSection,
    -- * parts of a problem
        ProblemNumber(..),
        ProblemDescription(..),
        ProblemReasonName(..),
        ForwardsReason(..),
        BackwardsReason(..),
        ProblemJustificationDegree(..),
        ProblemInterestDegree(..),
        ProblemStrengthDegree(..),
    -- * reason modifiers
        Direction(..),
        Defeasibility(..),
    -- * useful for tags
        ƮGivenPremise,
        ƮUltimateEpistemicInterest,
        ƮReason,
        ƮProblemVariables,
    -- * misc. don't know
        ReasonBlock,
        type Named,
        ProblemPremise,
        ProblemInterest,
        ForwardsPrimaFacieReason,
        ProblemForwardsPrimaFacieReason,
        ProblemForwardsConclusiveReason,
    -- * all the rest
        runSectionParser,
        decodeGivenPremisesSection,
        decodeUltimateEpistemicInterestsSection,
        decodeReasonSection,
        problemSectionText,
        parserProblemJustificationDegree,
        parserProblemInterestDegree,
        parserProblemVariablesText,
        parserProblemStrengthDegree,
        parserProblemReasonName,
        extractFromProblemReasonTextForwards,
        extractFromProblemReasonTextBackwards,
        enbracedListParser,
    ) where

import ClassyPrelude hiding (
    try,
    )
import Prelude                          (read)

import Control.Applicative              (many)
import Control.Conditional              (guardM)
import Control.Monad                    ((<=<))
import Text.Parsec                      (anyChar)
import Text.Parsec                      (char)
import Text.Parsec                      (eof)
import Text.Parsec                      (lookAhead)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (notFollowedBy)
import Text.Parsec                      (option)
import Text.Parsec                      (space)
import Text.Parsec                      (spaces)
import Text.Parsec                      (string)
import Text.Parsec                      (try)
import Text.Parsec.Text                 (Parser)

import Oscar.Formula                    (Formula)
import Oscar.Formula                    (formulaFromText)
import Oscar.ProblemDoubleParser        (LispPositiveDouble)
import Oscar.ProblemDoubleParser        (LispPositiveDouble(LispPositiveDouble))
import Oscar.ProblemDoubleParser        (parserLispPositiveDouble)
import Oscar.ProblemLocation            (ƇPlace)
import Oscar.ProblemLocation            (ƮAfter)
import Oscar.ProblemLocation            (ƮSection)
import Oscar.ProblemSection             (Section(Section'BackwardsConclusiveReasons))
import Oscar.ProblemSection             (Section(Section'BackwardsPrimaFacieReasons))
import Oscar.ProblemSection             (Section(Section'ForwardsConclusiveReasons))
import Oscar.ProblemSection             (Section(Section'ForwardsPrimaFacieReasons))
import Oscar.ProblemSection             (Section(Section'GivenPremises))
import Oscar.ProblemSection             (Section(Section'UltimateEpistemicInterests))
import Oscar.ProblemSection             (sectionParser)
import Oscar.ProblemSectionDecoder      (DecodedSection)
import Oscar.ProblemSectionDecoder      (decodeSection)
import Oscar.ProblemSectionDecoder      (HasSection)
import Oscar.ProblemSectionDecoder      (InjectiveSection)
import Oscar.ProblemSectionDecoder      (section)
import Oscar.ProblemStatefulParse       (runStatefulParse)
import Oscar.ProblemStatefulParse       (StatefulParse)
import Oscar.ProblemStatefulParse       (statefulParse)
import Oscar.Utilities                  (precededBy)
import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (unƭ)
import Oscar.Utilities                  (withInput)
import Oscar.Utilities                  (ƭ)
import Oscar.Utilities                  ((⊥))

data ƮProblemAfterNumberLabel

instance ƇPlace ProblemNumber where
instance ƇPlace ProblemDescription where

-- | This is the highest-level problem decoder available in this module.
problemsM ∷ FilePath ⁞ [Problem] → IO [Problem]
problemsM = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

data Problem = Problem
    { _problemNumber                     ∷ !ProblemNumber
    , _problemDescription                ∷ !ProblemDescription
    , _problemPremises                   ∷ ![ProblemPremise]
    , _problemInterests                  ∷ ![ProblemInterest]
    , _problemForwardsPrimaFacieReasons  ∷ ![(ProblemReasonName, ForwardsReason, ProblemStrengthDegree)]
    , _problemForwardsConclusiveReasons  ∷ ![(ProblemReasonName, ForwardsReason)]
    , _problemBackwardsPrimaFacieReasons ∷ ![(ProblemReasonName, BackwardsReason, ProblemStrengthDegree)]
    , _problemBackwardsConclusiveReasons ∷ ![(ProblemReasonName, BackwardsReason)]
    }
  deriving (Show)

-- | Read a file.
readProblemsTextFile ∷ (FilePath ⁞ [Problem])  -- ^ The input file is presumed to represent one or more problems...
                     → IO (Text ⁞ [Problem])   -- ^ as 'Text'. 'IO' obtained via 'readFile'.
readProblemsTextFile = map ƭ . readFile . unƭ

-- | Partition the concatenated problems so that each 'Text' block contains 
--   one 'Text' block for each 'Problem'.
partitionProblemsText ∷ (Text ⁞ [Problem])                 -- ^ 'Text'ual 'Problem's, possibly obtained from 'readProblemsTextFile'
                      → [Text ⁞ ƮProblemAfterNumberLabel]  -- ^ Results in one 'Text' block for each 'Problem'.
partitionProblemsText = simpleParse (many p) . unƭ
  where
    p ∷ Parser (Text ⁞ ƮProblemAfterNumberLabel)
    p = do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP

    endP ∷ Parser ()
    endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

-- | The formatting of the input is documented here (TODO).
problemFromText ∷ (Text ⁞ ƮProblemAfterNumberLabel)  -- ^ possibly as obtained from 'partitionProblemsText'
                → Problem
problemFromText t = Problem
    number
    description
    (decodeGivenPremisesSection pSTaD)
    (decodeUltimateEpistemicInterestsSection pSTaD)
    (decodeForwardsPrimaFacieReasonSection pSTaD)
    (decodeForwardsConclusiveReasonSection pSTaD)
    (decodeBackwardsPrimaFacieReasonSection pSTaD)
    (decodeBackwardsConclusiveReasonSection pSTaD)
  where
    (number, afterNumber) = runStatefulParse t

    (description, afterDescription) = runStatefulParse afterNumber

    decodedSection ∷ (HasSection kind, InjectiveSection kind decode) ⇒ decode
    decodedSection = decodeSection $ problemSectionText afterDescription

    pSTaD ∷ (HasSection kind) ⇒ Text ⁞ ƮSection kind 
    pSTaD = problemSectionText afterDescription

_rbProblemReasonName     (n, _, _, _) = n
_rbProblemReasonText     (_, t, _, _) = t
_rbProblemStrengthDegree (_, _, _, d) = d

decodeForwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards PrimaFacie) → [(ProblemReasonName, ForwardsReason, ProblemStrengthDegree)]
decodeForwardsPrimaFacieReasonSection = map fpfrts . decodeReasonSection
  where
    fpfrts ∷ ReasonBlock Forwards PrimaFacie → (ProblemReasonName, ForwardsReason, ProblemStrengthDegree)
    fpfrts rb = (,,)
        (_rbProblemReasonName rb)
        (fr $ _rbProblemReasonText rb)
        (_rbProblemStrengthDegree rb)
      where
        fr = uncurry ForwardsReason . booyah . unƭ . extractFromProblemReasonTextForwards
        booyah = first (map formulaFromText) . second formulaFromText

decodeForwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards Conclusive) → [(ProblemReasonName, ForwardsReason)]
decodeForwardsConclusiveReasonSection = map fpfrts' . decodeReasonSection
  where
    fpfrts' ∷ ReasonBlock Forwards Conclusive → (ProblemReasonName, ForwardsReason)
    fpfrts' rb = case _rbProblemStrengthDegree rb of
        ProblemStrengthDegree (LispPositiveDouble 1) -> result
        _ -> error "conclusive strength must = 1"
      where
        result = (,)
            (_rbProblemReasonName rb)
            (fr $ _rbProblemReasonText rb)
        fr = uncurry ForwardsReason . booyah . unƭ . extractFromProblemReasonTextForwards
        booyah = first (map formulaFromText) . second formulaFromText

decodeBackwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards PrimaFacie) → [(ProblemReasonName, BackwardsReason, ProblemStrengthDegree)]
decodeBackwardsPrimaFacieReasonSection = map bpfrts . decodeReasonSection
  where
    bpfrts ∷ ReasonBlock Backwards PrimaFacie → (ProblemReasonName, BackwardsReason, ProblemStrengthDegree)
    bpfrts rb = (,,)
        (_rbProblemReasonName rb)
        (br $ _rbProblemReasonText rb)
        (_rbProblemStrengthDegree rb)
      where
        br = booyah . unƭ . extractFromProblemReasonTextBackwards 

        booyah (fps, bps, c) = BackwardsReason (formulaFromText <$> fps) (formulaFromText <$> bps) (formulaFromText c)

decodeBackwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards Conclusive) → [(ProblemReasonName, BackwardsReason)]
decodeBackwardsConclusiveReasonSection = map bpfrts' . decodeReasonSection
  where
    bpfrts' ∷ ReasonBlock Backwards Conclusive → (ProblemReasonName, BackwardsReason)
    bpfrts' rb = case (_rbProblemStrengthDegree rb) of 
        ProblemStrengthDegree (LispPositiveDouble 1) -> result
        _ -> error "conclusive strength must = 1"
        
      where
        result = (,)
            (_rbProblemReasonName rb)
            (br $ _rbProblemReasonText rb)
        br = booyah . unƭ . extractFromProblemReasonTextBackwards 
        booyah (fps, bps, c) = BackwardsReason (formulaFromText <$> fps) (formulaFromText <$> bps) (formulaFromText c)


-- | A (hopefully) unique identifier of a 'Problem'.
newtype ProblemNumber = ProblemNumber Int
  deriving (Show)

-- | A (possibly empty) description of the problem.
newtype ProblemDescription = ProblemDescription Text
  deriving (Show)

newtype ProblemReasonName = ProblemReasonName Text
  deriving (Show)

data ForwardsReason = ForwardsReason 
    { _frForwardsPremises ∷ ![Formula]  -- ^ TODO [] -> Set
    , _frConclusion       ∷ !Formula    -- ^ conclusion
    }
  deriving (Show)

data BackwardsReason = BackwardsReason 
    { _brForwardsPremises  ∷ ![Formula] 
    , _brBackwardsPremises ∷ ![Formula]
    , _brConclusion        ∷ !Formula
    }
  deriving (Show)

newtype ProblemJustificationDegree = ProblemJustificationDegree LispPositiveDouble
  deriving (Show)

newtype ProblemInterestDegree = ProblemInterestDegree LispPositiveDouble
  deriving (Show)

newtype ProblemStrengthDegree = ProblemStrengthDegree LispPositiveDouble
  deriving (Show)

-- | The orientation of a reason.
data Direction 
    = Forwards   -- ^ For reasons that require matching premises to draw new conclusions
    | Backwards  -- ^ For reasons that require matching conclusions to draw new interests
  deriving (Show)

-- | 
data Defeasibility 
    = PrimaFacie  -- ^ For reasons whose conclusions can be undercut or rebutted
    | Conclusive  -- ^ For reasons whose conclusions are logical consequences of their premises
  deriving (Show)

data ƮGivenPremise

data ƮUltimateEpistemicInterest

data ƮReason (direction ∷ Direction) (defeasibility ∷ Defeasibility)

data ƮProblemVariables

type ReasonBlock (direction ∷ Direction) (defeasibility ∷ Defeasibility) = 
    (ProblemReasonName, (Text ⁞ ƮReason direction defeasibility), Text ⁞ ƮProblemVariables, ProblemStrengthDegree)

type family Named a ∷ *
type instance Named ForwardsPrimaFacieReason = (ProblemReasonName, ForwardsPrimaFacieReason)

type ProblemPremise                  = (Formula, ProblemJustificationDegree)
type ProblemInterest                 = (Formula, ProblemInterestDegree)
type ForwardsPrimaFacieReason        = (ForwardsReason, ProblemStrengthDegree)
type ProblemForwardsPrimaFacieReason = Named ForwardsPrimaFacieReason
type ProblemForwardsConclusiveReason = (ProblemReasonName, ForwardsReason)

-- | The 'ProblemNumber' is identified at the top of the text block
instance StatefulParse ProblemNumber ƮProblemAfterNumberLabel (ƮAfter ProblemNumber) where
    statefulParse = ƭ $ ProblemNumber . read <$> 
        manyTill anyChar (lookAhead . try $ space)

-- | Parsing of the problem description starts immediately after the problem number and leaves the parser in a location immediately after the description.
instance StatefulParse ProblemDescription 
                       (ƮAfter ProblemNumber)
                       (ƮAfter ProblemDescription)
  where
    statefulParse = ƭ $ spaces >> ProblemDescription . pack <$> p
      where
        p = manyTill anyChar $ lookAhead . try $ spaces >> sectionParser

runSectionParser ∷ Parser s → Text ⁞ ƮSection a → [s]
runSectionParser p = simpleParse (many (try p) <* many space <* eof) . unƭ

-- | 
decodeGivenPremisesSection ∷ Text ⁞ ƮSection ƮGivenPremise 
                           → [(Formula, ProblemJustificationDegree)]
decodeGivenPremisesSection = runSectionParser p
  where
    p ∷ Parser (Formula, ProblemJustificationDegree)
    p = do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
        return (formulaFromText . pack $ t, d)

decodeUltimateEpistemicInterestsSection ∷ Text ⁞ ƮSection ƮUltimateEpistemicInterest 
                                        → [(Formula, ProblemInterestDegree)]
decodeUltimateEpistemicInterestsSection = runSectionParser $ do
    spaces
    (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
    return (formulaFromText . pack $ t, d)


decodeReasonSection ∷ Text ⁞ ƮSection (ƮReason direction defeasibility)
                    → [(ProblemReasonName, (Text ⁞ ƮReason direction defeasibility), Text ⁞ ƮProblemVariables, ProblemStrengthDegree)]
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

instance HasSection ƮGivenPremise                  where section _ = Section'GivenPremises
instance HasSection ƮUltimateEpistemicInterest     where section _ = Section'UltimateEpistemicInterests
instance HasSection (ƮReason Forwards  PrimaFacie) where section _ = Section'ForwardsPrimaFacieReasons
instance HasSection (ƮReason Forwards  Conclusive) where section _ = Section'ForwardsConclusiveReasons
instance HasSection (ƮReason Backwards PrimaFacie) where section _ = Section'BackwardsPrimaFacieReasons
instance HasSection (ƮReason Backwards Conclusive) where section _ = Section'BackwardsConclusiveReasons

problemSectionText ∷ 
    ∀ kind. (HasSection kind) ⇒
    Text ⁞ ƮAfter ProblemDescription → 
    Text ⁞ ƮSection kind
problemSectionText = ƭ . rawSection (section $ ((⊥) ∷ kind)) . unƭ
  where
    rawSection ∷ Section → Text → Text
    rawSection _section = simpleParse $ do
        _ ← manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== _section) sectionParser)
        p' <|> pure (pack "")
      where
        p' ∷ Parser Text
        p' = do
            guardM (map (== _section) sectionParser)
            pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

parserProblemJustificationDegree ∷ Parser ProblemJustificationDegree
parserProblemJustificationDegree = ProblemJustificationDegree <$> (many space *> string "justification" *> many space *> char '=' *> parserLispPositiveDouble)

parserProblemInterestDegree ∷ Parser ProblemInterestDegree
parserProblemInterestDegree = ProblemInterestDegree <$> (many space *> string "interest" *> many space *> char '=' *> parserLispPositiveDouble)

parserProblemVariablesText ∷ Parser (Text ⁞ ƮProblemVariables)
parserProblemVariablesText = ƭ . pack <$> (option "" . try $ many space *> string "variables" *> many space *> char '=' *> many space *> char '{' *> manyTill anyChar (lookAhead . try $ char '}') <* char '}')

parserProblemStrengthDegree ∷ Parser ProblemStrengthDegree
parserProblemStrengthDegree = ProblemStrengthDegree <$> (many space *> string "strength" *> many space *> char '=' *> parserLispPositiveDouble)

parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> (many space *> manyTill anyChar (lookAhead . try $ char ':') <* char ':')

extractFromProblemReasonTextForwards ∷
    Text ⁞ ƮReason Forwards defeasibility →
    ([Text], Text) ⁞ ƮReason Forwards defeasibility
extractFromProblemReasonTextForwards = ƭ . simpleParse p . unƭ
  where
    p ∷ Parser ([Text], Text)
    p = do
        (premiseTexts, _) ← enbracedListParser `precededBy` (many space >> string "||=>" >> many space)
        conclusionText ← pack <$> many anyChar
        return (premiseTexts, conclusionText)

extractFromProblemReasonTextBackwards ∷
    Text ⁞ ƮReason Backwards defeasibility →
    ([Text], [Text], Text) ⁞ ƮReason Backwards defeasibility
extractFromProblemReasonTextBackwards = ƭ . simpleParse p . unƭ
  where
    p ∷ Parser ([Text], [Text], Text)
    p = do
        forwardsPremiseTextsText ← manyTill anyChar (lookAhead . try $ (many space >> char '{' >> many (notFollowedBy (char '}') >> anyChar) >> char '}' >> many space >> string "||=>" >> many space))
        forwardsPremiseTexts ← withInput (pack forwardsPremiseTextsText) enbracedListParser
        spaces
        (backwardsPremiseTexts, _) ← enbracedListParser `precededBy` (many space >> string "||=>" >> many space)
        conclusionText ← pack <$> many anyChar
        return (forwardsPremiseTexts, backwardsPremiseTexts, conclusionText)

enbracedListParser ∷ Parser [Text]
enbracedListParser = do
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
