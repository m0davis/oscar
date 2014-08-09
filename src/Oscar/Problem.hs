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
    -- * internal
    module Oscar.Problem
    ) where

import ClassyPrelude hiding (
    try,
    undefined,
    )
import Prelude                          (read)
import Prelude                          (undefined)

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
import Oscar.ProblemDoubleParser        (parserLispPositiveDouble)
import Oscar.ProblemLocation            (ƇPlace)
import Oscar.ProblemLocation            (ƮAfter)
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
import Oscar.ProblemSectionDecoder      (IsAKind)
import Oscar.ProblemSectionDecoder      (section)
import Oscar.ProblemSectionDecoder      (ƮSection)
import Oscar.ProblemStatefulParse       (runStatefulParse)
import Oscar.ProblemStatefulParse       (StatefulParse)
import Oscar.ProblemStatefulParse       (statefulParse)
import Oscar.Utilities                  (precededBy)
import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (unƭ)
import Oscar.Utilities                  (withInput)
import Oscar.Utilities                  (ƭ)

instance ƇPlace ProblemNumber where
instance ƇPlace ProblemDescription where

-- | Read a file.
problemsTextM ∷ (FilePath ⁞ [Problem])  
              -- ^ The input file is presumed to represent one or more
              --   problems...
              → IO (Text ⁞ [Problem])   
              -- ^ as 'Text'. 'IO' obtained via 'readFile'.
problemsTextM = map ƭ . readFile . unƭ

-- | Partition the concatenated problems so that each 'Text' block contains 
--   one 'Text' block for each 'Problem'.
problemTexts ∷ (Text ⁞ [Problem])  -- ^ 'Text'ual 'Problem's, possibly 
                                   --    obtained from 'problemsTextM'
             → [Text ⁞ Problem]    -- ^ Results in one 'Text' block for each 
                                   --  'Problem'.
problemTexts = simpleParse (many p) . unƭ
  where
    p ∷ Parser (Text ⁞ Problem)
    p = do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP

    endP ∷ Parser ()
    endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

-- | The formatting of the input is documented here (TODO).
problem ∷ (Text ⁞ Problem)  -- ^ possibly as obtained from 'problemTexts'
        → Problem
problem t = Problem
    number
    description
    (first (formulaFromText . unƭ) <$> (decodedSection ∷ DecodedSection GivenPremises))
    (first (formulaFromText . unƭ) <$> (decodedSection ∷ DecodedSection UltimateEpistemicInterests))
    (fpfrts <$> (decodedSection ∷ DecodedSection (Reasons Forwards PrimaFacie)))
    (fpfrts <$> (decodedSection ∷ DecodedSection (Reasons Forwards Conclusive)))
    (bpfrts <$> (decodedSection ∷ DecodedSection (Reasons Backwards Conclusive)))
    (bpfrts <$> (decodedSection ∷ DecodedSection (Reasons Backwards Conclusive)))
  where
    (number, afterNumber) = runStatefulParse t

    (description, afterDescription) = runStatefulParse afterNumber

    decodedSection ∷ (HasSection kind, InjectiveSection kind decode) ⇒ decode
    decodedSection = decodeSection $ problemSectionText afterDescription

-- | A (hopefully) unique identifier of a 'Problem'.
newtype ProblemNumber = ProblemNumber Int
  deriving (Show)

-- | The 'ProblemNumber' is identified at the top of the text block
instance StatefulParse ProblemNumber Problem (ƮAfter ProblemNumber) where
    statefulParse = ƭ $ ProblemNumber . read <$> 
        manyTill anyChar (lookAhead . try $ space)

-- | 
newtype ProblemDescription = ProblemDescription Text
  deriving (Show)

-- | Parsing of the problem description starts immediately after the problem number and leaves the parser in a location immediately after the description.
instance StatefulParse ProblemDescription 
                       (ƮAfter ProblemNumber)
                       (ƮAfter ProblemDescription)
  where
    statefulParse = ƭ $ spaces >> ProblemDescription . pack <$> p
      where
        p = manyTill anyChar $ lookAhead . try $ spaces >> sectionParser

-- | 
instance IsAKind GivenPremises
instance IsAKind UltimateEpistemicInterests
instance IsAKind (Reasons direction defeasible)

instance InjectiveSection GivenPremises 
                          [(Text ⁞ ƮGivenPremise, ProblemJustificationDegree)] 
  where
    type DecodedSection GivenPremises = [(Text ⁞ ƮGivenPremise, ProblemJustificationDegree)]
    decodeSection = simpleParse (many (try p) <* many space <* eof) . unƭ
      where
        p ∷ Parser (Text ⁞ ƮGivenPremise, ProblemJustificationDegree)
        p = do
            spaces
            (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
            return (ƭ . pack $ t, d)

instance InjectiveSection UltimateEpistemicInterests [(Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)] where
    type DecodedSection UltimateEpistemicInterests = [(Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)]
    decodeSection = simpleParse (many (try p) <* many space <* eof) . unƭ
      where
        p ∷ Parser (Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)
        p = do
            spaces
            (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
            return (ƭ . pack $ t, d)

instance InjectiveSection (Reasons direction defeasible) [ReasonBlock direction defeasible] where
    type DecodedSection (Reasons direction defeasible) = [ReasonBlock direction defeasible]
    decodeSection = simpleParse (many (try p) <* many space <* eof) . unƭ
      where
        p ∷ Parser (ReasonBlock direction defeasible)
        p = do
            n ← parserProblemReasonName
            spaces
            (t, (v, d)) ← many anyChar `precededBy` p'
            return $ ReasonBlock n (ƭ . (pack ∷ String → Text) $ t) v d
          where
            p' ∷ Parser (Text ⁞ ƮProblemVariables, ProblemStrengthDegree)
            p' = do
                t ← parserProblemVariablesText
                d ← parserProblemStrengthDegree
                return (t, d)

data GivenPremises
data UltimateEpistemicInterests

data Direction = Forwards | Backwards
  deriving (Show)

data Defeasibility = PrimaFacie | Conclusive
  deriving (Show)

data Reasons (direction ∷ Direction) (defeasible ∷ Defeasibility)

instance HasSection GivenPremises                  where section _ = Section'GivenPremises
instance HasSection UltimateEpistemicInterests     where section _ = Section'UltimateEpistemicInterests
instance HasSection (Reasons Forwards  PrimaFacie) where section _ = Section'ForwardsPrimaFacieReasons
instance HasSection (Reasons Forwards  Conclusive) where section _ = Section'ForwardsConclusiveReasons
instance HasSection (Reasons Backwards PrimaFacie) where section _ = Section'BackwardsPrimaFacieReasons
instance HasSection (Reasons Backwards Conclusive) where section _ = Section'BackwardsConclusiveReasons

problemSectionText ∷ 
    ∀ kind. (HasSection kind) ⇒
    Text ⁞ ƮAfter ProblemDescription → 
    Text ⁞ ƮSection kind
problemSectionText = ƭ . rawSection (section kind) . unƭ
  where
    kind ∷ kind = undefined

    rawSection ∷ Section → Text → Text
    rawSection _section = simpleParse $ do
        _ ← manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== _section) sectionParser)
        p' <|> pure (pack "")
      where
        p' ∷ Parser Text
        p' = do
            guardM (map (== _section) sectionParser)
            pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

--
newtype ProblemJustificationDegree = ProblemJustificationDegree LispPositiveDouble
  deriving (Show)

parserProblemJustificationDegree ∷ Parser ProblemJustificationDegree
parserProblemJustificationDegree = ProblemJustificationDegree <$> (many space *> string "justification" *> many space *> char '=' *> parserLispPositiveDouble)

--
data ƮGivenPremise

--
newtype ProblemInterestDegree = ProblemInterestDegree LispPositiveDouble
  deriving (Show)

parserProblemInterestDegree ∷ Parser ProblemInterestDegree
parserProblemInterestDegree = ProblemInterestDegree <$> (many space *> string "interest" *> many space *> char '=' *> parserLispPositiveDouble)

--
data ƮUltimateEpistemicInterest

--
data ƮProblemVariables

parserProblemVariablesText ∷ Parser (Text ⁞ ƮProblemVariables)
parserProblemVariablesText = ƭ . pack <$> (option "" . try $ many space *> string "variables" *> many space *> char '=' *> many space *> char '{' *> manyTill anyChar (lookAhead . try $ char '}') <* char '}')

--
newtype ProblemStrengthDegree = ProblemStrengthDegree LispPositiveDouble
  deriving (Show)

parserProblemStrengthDegree ∷ Parser ProblemStrengthDegree
parserProblemStrengthDegree = ProblemStrengthDegree <$> (many space *> string "strength" *> many space *> char '=' *> parserLispPositiveDouble)

--
newtype ProblemReasonName = ProblemReasonName Text
  deriving (Show)

parserProblemReasonName ∷ Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> (many space *> manyTill anyChar (lookAhead . try $ char ':') <* char ':')

--
data ƮReason (direction ∷ Direction) (defeasible ∷ Defeasibility)

data ReasonBlock (direction ∷ Direction) (defeasible ∷ Defeasibility) = ReasonBlock
    {   _rbProblemReasonName     ∷ !ProblemReasonName
    ,   _rbProblemReasonText     ∷ !(Text ⁞ ƮReason direction defeasible)
    ,   _rbProblemVariablesText  ∷ !(Text ⁞ ƮProblemVariables)
    ,   _rbProblemStrengthDegree ∷ !ProblemStrengthDegree
    }
  deriving (Show)

extractFromProblemReasonTextForwards ∷
    Text ⁞ ƮReason Forwards defeasible →
    ([Text], Text) ⁞ ƮReason Forwards defeasible
extractFromProblemReasonTextForwards = ƭ . simpleParse p . unƭ
  where
    p ∷ Parser ([Text], Text)
    p = do
        (premiseTexts, _) ← enbracedListParser `precededBy` (many space >> string "||=>" >> many space)
        conclusionText ← pack <$> many anyChar
        return (premiseTexts, conclusionText)

extractFromProblemReasonTextBackwards ∷
    Text ⁞ ƮReason Backwards defeasible →
    ([Text], [Text], Text) ⁞ ƮReason Backwards defeasible
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

--
data ForwardsReason = ForwardsReason ![Formula] !Formula -- TODO [] -> Set
  deriving (Show)

data BackwardsReason = BackwardsReason ![Formula] ![Formula] !Formula
  deriving (Show)

--
data Problem = Problem
    { _problemNumber              ∷ !ProblemNumber
    , _problemDescription         ∷ !ProblemDescription
    , _premises                   ∷ ![(Formula, ProblemJustificationDegree)]
    , _interests                  ∷ ![(Formula, ProblemInterestDegree)]
    , _forwardsPrimaFacieReasons  ∷ ![(ProblemReasonName, ForwardsReason, ProblemStrengthDegree)]
    , _forwardsConclusiveReasons  ∷ ![(ProblemReasonName, ForwardsReason, ProblemStrengthDegree)] -- TODO: strength must always be 1
    , _backwardsPrimaFacieReasons ∷ ![(ProblemReasonName, BackwardsReason, ProblemStrengthDegree)]
    , _backwardsConclusiveReasons ∷ ![(ProblemReasonName, BackwardsReason, ProblemStrengthDegree)] -- TODO: strength must always be 1
    }
  deriving (Show)

fpfrts ∷ ReasonBlock Forwards defeasible → (ProblemReasonName, ForwardsReason, ProblemStrengthDegree)
fpfrts rb = (,,)
    (_rbProblemReasonName rb)
    (fr $ _rbProblemReasonText rb)
    (_rbProblemStrengthDegree rb)
  where
    fr = uncurry ForwardsReason . booyah . unƭ . extractFromProblemReasonTextForwards
    booyah = first (map formulaFromText) . second formulaFromText


bpfrts ∷ ∀ defeasible. ReasonBlock Backwards defeasible → (ProblemReasonName, BackwardsReason, ProblemStrengthDegree)
bpfrts rb = (,,)
    (_rbProblemReasonName rb)
    (br $ _rbProblemReasonText rb)
    (_rbProblemStrengthDegree rb)
  where
    br = booyah . unƭ . extractFromProblemReasonTextBackwards 

    booyah (fps, bps, c) = BackwardsReason (formulaFromText <$> fps) (formulaFromText <$> bps) (formulaFromText c)

-- | This is the highest-level problem decoder available in this module.
problemsM ∷ FilePath ⁞ [Problem] → IO [Problem]
problemsM = return . map problem . problemTexts <=< problemsTextM
