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
module Oscar.Problem.Internal.Internal (
    -- * primitive API, in order of intended usage
    readProblemsTextFile,
    partitionProblemsText,
    statefulParseProblemNumber,
    statefulParseProblemDescription,
    problemSectionText,
    decodeGivenPremisesSection,
    decodeUltimateEpistemicInterestsSection,
    decodeForwardsPrimaFacieReasonSection,
    decodeForwardsConclusiveReasonSection,
    decodeBackwardsPrimaFacieReasonSection,
    decodeBackwardsConclusiveReasonSection,
    -- * helper API for statefulParse...
    runStatefulParse',
    parseProblemNumber,
    parseProblemDescription,
    -- * helper API for decode...Section
    -- ** all sections
    runSectionParser,
    -- ** reason sections
    decodeReasonSection,    
    getForwardsReason,
    getBackwardsReason,
    -- * Problem data
    Problem(..),
    -- * stateful stuff
    runStatefulParse',
    parseProblemNumber,
    parseProblemDescription,
    -- * parts of a problem
        -- ** ProblemNumber
        ProblemNumber(..),
        statefulParseProblemNumber,
        -- ** ProblemDescription
        ProblemDescription(..),
        statefulParseProblemDescription,
        -- ** ReasonSection  
        ReasonSection,
        _rsProblemReasonName,
        _rsProblemReasonText,
        _rsProblemVariables,
        _rsProblemStrengthDegree,
        decodeReasonSection,
        -- ** premises, interests, reasons
        ProblemPremise,
        ProblemInterest,
        ProblemForwardsPrimaFacieReason,
        ProblemForwardsConclusiveReason,
        ProblemBackwardsPrimaFacieReason,
        ProblemBackwardsConclusiveReason,
            -- *** parts of a reason
            ProblemReasonName(..),
            ForwardsReason(..),
            BackwardsReason(..),
        -- ** degrees
        ProblemJustificationDegree(..),
        ProblemInterestDegree(..),
        ProblemStrengthDegree(..),
    -- * API
        -- ** highest-level
        problemsM,
        -- ** other
        readProblemsTextFile,
        partitionProblemsText,
        problemFromText,
    -- * section decoders
    decodeGivenPremisesSection,
    decodeUltimateEpistemicInterestsSection,
    decodeForwardsPrimaFacieReasonSection,
    decodeForwardsConclusiveReasonSection,
    decodeBackwardsPrimaFacieReasonSection,
    decodeBackwardsConclusiveReasonSection,
    -- * reason parsers
    getForwardsReason,
    getBackwardsReason,
    -- * reason modifiers
    Direction(..),
    Defeasibility(..),
    -- * useful for tags
    ƮProblemAfterNumberLabel,
    ƮProblemAfterNumber,
    ƮProblemAfterDescription,
    ƮGivenPremise,
    ƮUltimateEpistemicInterest,
    ƮReason,
    ƮProblemVariables,
    -- * parsers
    parserProblemJustificationDegree,
    parserProblemInterestDegree,
    parserProblemVariablesText,
    parserProblemStrengthDegree,
    parserProblemReasonName,
    parserEnbracedTexts,
    -- * all the rest
    runSectionParser,
    problemSectionText,
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

-- | A Problem reflects exactly as much information as is parsed from a Text of an OSCAR problem
data Problem = Problem
    { _problemNumber                     ∷ !ProblemNumber
    , _problemDescription                ∷ !ProblemDescription
    , _problemPremises                   ∷ ![ProblemPremise]
    , _problemInterests                  ∷ ![ProblemInterest]
    , _problemForwardsPrimaFacieReasons  ∷ ![ProblemForwardsPrimaFacieReason]
    , _problemForwardsConclusiveReasons  ∷ ![ProblemForwardsConclusiveReason]
    , _problemBackwardsPrimaFacieReasons ∷ ![ProblemBackwardsPrimaFacieReason]
    , _problemBackwardsConclusiveReasons ∷ ![ProblemBackwardsConclusiveReason]
    }
  deriving (Show)

-- | A (hopefully) unique identifier of a 'Problem'.
newtype ProblemNumber = ProblemNumber Int
  deriving (Show)

statefulParseProblemNumber ∷ 
    Text ⁞ ƮProblemAfterNumberLabel → 
    (ProblemNumber, Text ⁞ ƮProblemAfterNumber)
statefulParseProblemNumber = runStatefulParse' parseProblemNumber

parseProblemNumber ∷ Parser ProblemNumber ⁞ ƮProblemAfterNumberLabel
parseProblemNumber = ƭ $ ProblemNumber . read <$> 
    manyTill anyChar (lookAhead . try $ space)

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


-- | The 'ProblemNumber' is identified at the top of the text block
--instance StatefulParse ProblemNumber 
--                       ƮProblemAfterNumberLabel 
--                       ƮProblemAfterNumber 
--  where
--    statefulParse = ƭ $ ProblemNumber . read <$> 
--        manyTill anyChar (lookAhead . try $ space)

-- | A (possibly empty) description of the problem.
newtype ProblemDescription = ProblemDescription Text
  deriving (Show)

statefulParseProblemDescription ∷ Text ⁞ ƮProblemAfterNumber → (ProblemDescription, Text ⁞ ƮProblemAfterDescription)
statefulParseProblemDescription = runStatefulParse' parseProblemDescription

---- | Parsing of the problem description starts immediately after the problem number and leaves the parser in a location immediately after the description.
--instance StatefulParse ProblemDescription 
--                       ƮProblemAfterNumber
--                       ƮProblemAfterDescription
--  where
--    statefulParse = ƭ $ spaces >> ProblemDescription . pack <$> p
--      where
--        p = manyTill anyChar $ lookAhead . try $ spaces >> sectionParser

parseProblemDescription ∷ Parser ProblemDescription ⁞ ƮProblemAfterNumber
parseProblemDescription = ƭ $ spaces >> ProblemDescription . pack <$> p
  where
    p = manyTill anyChar $ lookAhead . try $ spaces >> sectionParser

-- | A formula for a premise with its justification
type ProblemPremise                   = (Formula, ProblemJustificationDegree)

-- | A formula for an interest with its degree of interest
type ProblemInterest                  = (Formula, ProblemInterestDegree)

-- | A forwards p.f. reason with its name and strength
type ProblemForwardsPrimaFacieReason  = (ProblemReasonName, ForwardsReason, ProblemStrengthDegree)

-- | A forwards conclusive reason with its name (the strength is unity, implicitly)
type ProblemForwardsConclusiveReason  = (ProblemReasonName, ForwardsReason)

-- | A backwards p.f. reason with its name and strength
type ProblemBackwardsPrimaFacieReason = (ProblemReasonName, BackwardsReason, ProblemStrengthDegree)

-- | A backwards conclusive reason with its name (the strength is unity, implicitly)
type ProblemBackwardsConclusiveReason = (ProblemReasonName, BackwardsReason)

-- | A name for a reason
newtype ProblemReasonName = ProblemReasonName Text
  deriving (Show)

-- | A forwards reason
data ForwardsReason = ForwardsReason 
    { _frForwardsPremises ∷ ![Formula]  -- ^ TODO [] -> Set
    , _frConclusion       ∷ !Formula    -- ^ conclusion
    }
  deriving (Show)

-- | A backwards reason
data BackwardsReason = BackwardsReason 
    { _brForwardsPremises  ∷ ![Formula] 
    , _brBackwardsPremises ∷ ![Formula]
    , _brConclusion        ∷ !Formula
    }
  deriving (Show)

-- | The degree of justification (of a premise)
newtype ProblemJustificationDegree = ProblemJustificationDegree LispPositiveDouble
  deriving (Show)

-- | The degree of interest (of an interest)
newtype ProblemInterestDegree = ProblemInterestDegree LispPositiveDouble
  deriving (Show)

-- | The strength (of a reason)
newtype ProblemStrengthDegree = ProblemStrengthDegree LispPositiveDouble
  deriving (Show)

-- | This is the highest-level problem decoder available in this module.
problemsM ∷ FilePath ⁞ [Problem] → IO [Problem]
problemsM = return . map problemFromText . partitionProblemsText <=< readProblemsTextFile

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
    (number, afterNumber) = statefulParseProblemNumber t
    (description, afterDescription) = statefulParseProblemDescription afterNumber

    pSTaD ∷ (HasSection kind) ⇒ Text ⁞ ƮSection kind 
    pSTaD = problemSectionText afterDescription

-- | 
decodeGivenPremisesSection ∷ Text ⁞ ƮSection ƮGivenPremise 
                           → [ProblemPremise]
decodeGivenPremisesSection = runSectionParser p
  where
    p ∷ Parser (Formula, ProblemJustificationDegree)
    p = do
        spaces
        (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
        return (formulaFromText . pack $ t, d)

-- | 
decodeUltimateEpistemicInterestsSection ∷ Text ⁞ ƮSection ƮUltimateEpistemicInterest 
                                        → [ProblemInterest]
decodeUltimateEpistemicInterestsSection = runSectionParser $ do
    spaces
    (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
    return (formulaFromText . pack $ t, d)

-- | 
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

-- | 
decodeForwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards PrimaFacie) → [ProblemForwardsPrimaFacieReason]
decodeForwardsPrimaFacieReasonSection = map fpfrts . decodeReasonSection
  where
    fpfrts ∷ ReasonSection Forwards PrimaFacie → ProblemForwardsPrimaFacieReason
    fpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getForwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | 
decodeForwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Forwards Conclusive) → [ProblemForwardsConclusiveReason]
decodeForwardsConclusiveReasonSection = map fpfrts' . decodeReasonSection
  where
    fpfrts' ∷ ReasonSection Forwards Conclusive → ProblemForwardsConclusiveReason
    fpfrts' rb = case _rsProblemStrengthDegree rb of
        ProblemStrengthDegree (LispPositiveDouble 1) -> result
        _ -> error "conclusive strength must = 1"
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getForwardsReason $ _rsProblemReasonText rb)

-- | 
decodeBackwardsPrimaFacieReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards PrimaFacie) → [ProblemBackwardsPrimaFacieReason]
decodeBackwardsPrimaFacieReasonSection = map bpfrts . decodeReasonSection
  where
    bpfrts ∷ ReasonSection Backwards PrimaFacie → ProblemBackwardsPrimaFacieReason
    bpfrts rb = (,,)
        (_rsProblemReasonName rb)
        (getBackwardsReason $ _rsProblemReasonText rb)
        (_rsProblemStrengthDegree rb)

-- | 
decodeBackwardsConclusiveReasonSection ∷ Text ⁞ ƮSection (ƮReason Backwards Conclusive) → [ProblemBackwardsConclusiveReason]
decodeBackwardsConclusiveReasonSection = map bpfrts' . decodeReasonSection
  where
    bpfrts' ∷ ReasonSection Backwards Conclusive → ProblemBackwardsConclusiveReason
    bpfrts' rb = case (_rsProblemStrengthDegree rb) of 
        ProblemStrengthDegree (LispPositiveDouble 1) -> result
        _ -> error "conclusive strength must = 1"
        
      where
        result = (,)
            (_rsProblemReasonName rb)
            (getBackwardsReason $ _rsProblemReasonText rb)

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

-- | The orientation of a reason.
data Direction 
    = Forwards   -- ^ For reasons that require matching premises to draw new conclusions
    | Backwards  -- ^ For reasons that require matching conclusions to draw new interests
  deriving (Show)

-- | The defeasibility of a reason
data Defeasibility 
    = PrimaFacie  -- ^ For reasons whose conclusions can be undercut or rebutted
    | Conclusive  -- ^ For reasons whose conclusions are logical consequences of their premises
  deriving (Show)

-- | Stuff after the "Problem #"
data ƮProblemAfterNumberLabel

-- | Stuff after the "Problem #<number>"
data ƮProblemAfterNumber

-- | Stuff after the "Problem #<number>\n<description>" (and starting at the first section)
data ƮProblemAfterDescription

-- | The premise section
data ƮGivenPremise

instance HasSection ƮGivenPremise                  where section _ = Section'GivenPremises

-- | The interest section
data ƮUltimateEpistemicInterest

instance HasSection ƮUltimateEpistemicInterest     where section _ = Section'UltimateEpistemicInterests

-- | A reason section
data ƮReason (direction ∷ Direction) (defeasibility ∷ Defeasibility)

instance HasSection (ƮReason Forwards  PrimaFacie) where section _ = Section'ForwardsPrimaFacieReasons
instance HasSection (ƮReason Forwards  Conclusive) where section _ = Section'ForwardsConclusiveReasons
instance HasSection (ƮReason Backwards PrimaFacie) where section _ = Section'BackwardsPrimaFacieReasons
instance HasSection (ƮReason Backwards Conclusive) where section _ = Section'BackwardsConclusiveReasons

-- | Variables for a reason
data ƮProblemVariables

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

runSectionParser ∷ Parser s → Text ⁞ ƮSection a → [s]
runSectionParser p = simpleParse (many (try p) <* many space <* eof) . unƭ

-- | Gets the text of a particular section from all of the text following the description
-- e.g. given the input @ Text ⁞ ƮProblemAfterDescription @:
-- 
-- @
-- Given premises:
--      P    justification = 1.0
--      A    justification = 1.0
-- Ultimate epistemic interests:
--      R    interest = 1.0
--
--    FORWARDS PRIMA FACIE REASONS
--      pf-reason_1:   {P} ||=> Q   strength = 1.0
--      pf-reason_2:   {Q} ||=> R   strength = 1.0
--      pf-reason_3:   {C} ||=> ~R   strength = 1.0
--      pf-reason_4:   {B} ||=> C   strength = 1.0
--      pf-reason_5:   {A} ||=> B   strength = 1.0
-- @
--
-- we get the @ Text ⁞ ƮSection ƮGivenPremise @:
--
-- @
--      P    justification = 1.0
--      A    justification = 1.0
-- @
problemSectionText ∷ 
    ∀ kind. (HasSection kind) ⇒
    Text ⁞ ƮProblemAfterDescription → 
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
