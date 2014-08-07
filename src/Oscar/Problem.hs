{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.Problem where

import ClassyPrelude hiding (
    try,
    undefined,
    )
import Prelude                          (undefined)

import Control.Applicative              (empty)
import Control.Applicative              (many)
import Control.Conditional              (guardM)
import Control.Monad                    (mzero)
import Data.Coerce                      (coerce)
import Prelude                          (read)
import Text.Parsec                      (anyChar)
import Text.Parsec                      (char)
import Text.Parsec                      (eof)
import Text.Parsec                      (getInput)
import Text.Parsec                      (lookAhead)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (notFollowedBy)
import Text.Parsec                      (option)
import Text.Parsec                      (runParser)
import Text.Parsec                      (space)
import Text.Parsec                      (spaces)
import Text.Parsec                      (string)
import Text.Parsec                      (try)
import Text.Parsec.Text                 (Parser)
import Text.Show.Pretty                 (ppShow)

import Oscar.Formula                    (formulaFromText)
import Oscar.Formula                    (Formula)
import Oscar.Utilities                  (messageFromShow)
import Oscar.Utilities                  (messageFromShows)
import Oscar.Utilities                  (messageFromShows10)
import Oscar.Utilities                  (precededBy)
import Oscar.Utilities                  (simpleParse)
import Oscar.Utilities                  (withInput)
import Oscar.Utilities                  (type (⁞))
import Oscar.Utilities                  (ƭ)
import Oscar.Utilities                  (unƭ)

--
data ƮProblem

problemsTextM ∷ FilePath ⁞ [ƮProblem] → IO (Text ⁞ [ƮProblem])
problemsTextM = map ƭ . readFile . unƭ

--
problemTexts ∷ Text ⁞ [ƮProblem] → [Text ⁞ ƮProblem]
problemTexts = simpleParse (many p) . unƭ
  where
    p ∷ Parser (Text ⁞ ƮProblem)
    p = do
        spaces
        _ ← string "Problem #"
        ƭ . pack <$> manyTill anyChar endP

    endP ∷ Parser ()
    endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

--

class ƇPlace place where

instance ƇPlace ProblemNumber where
instance ƇPlace ProblemDescription where

data ƇPlace place ⇒ ƮAfter place

newtype ProblemNumber = ProblemNumber Int
  deriving (Show)

class StatefulParse value state1 state2 | value state1 → state2 where
    statefulParse ∷ Parser value ⁞ state1

    runStatefulParse ∷ Text ⁞ state1 → (value, Text ⁞ state2)
    runStatefulParse = simpleParse p' . unƭ
      where
        p' ∷ Parser (value, Text ⁞ state2)
        p' = do
            v ← unƭ (statefulParse ∷ Parser value ⁞ state1)
            r ← pack <$> many anyChar
            return (v, ƭ r)

instance StatefulParse ProblemNumber ƮProblem (ƮAfter ProblemNumber) where
    statefulParse = ƭ $ ProblemNumber . read <$> 
        manyTill anyChar (lookAhead . try $ space)

--
data Section
    = Section'GivenPremises
    | Section'UltimateEpistemicInterests
    | Section'ForwardsPrimaFacieReasons
    | Section'ForwardsConclusiveReasons
    | Section'BackwardsPrimaFacieReasons
    | Section'BackwardsConclusiveReasons
  deriving (Eq, Show)

sectionParser ∷ Parser Section
sectionParser =
    empty
    <|> string "Given premises:"               **> Section'GivenPremises
    <|> string "Ultimate epistemic interests:" **> Section'UltimateEpistemicInterests
    <|> string "FORWARDS PRIMA FACIE REASONS"  **> Section'ForwardsPrimaFacieReasons
    <|> string "FORWARDS CONCLUSIVE REASONS"   **> Section'ForwardsConclusiveReasons
    <|> string "BACKWARDS PRIMA FACIE REASONS" **> Section'BackwardsPrimaFacieReasons
    <|> string "BACKWARDS CONCLUSIVE REASONS"  **> Section'BackwardsConclusiveReasons
  where
    (**>) ∷ Parser a → b → Parser b
    p **> t = try p *> pure t

--
newtype ProblemDescription = ProblemDescription Text
  deriving (Show)

instance StatefulParse ProblemDescription (ƮAfter ProblemNumber) (ƮAfter ProblemDescription) where
    statefulParse = ƭ $ do 
        spaces
        ProblemDescription . pack <$> manyTill anyChar (lookAhead . try $ many space >> sectionParser)

--
class IsAKind k where

instance IsAKind GivenPremises
instance IsAKind UltimateEpistemicInterests
instance IsAKind (Reasons direction defeasible)

class InjectiveSection kind decode | {-kind → decode,-} decode → kind where
    decodeSection ∷ Text ⁞ ƮSection kind → decode

type family DecodedSection kind
type instance DecodedSection GivenPremises = [(Text ⁞ ƮGivenPremise, ProblemJustificationDegree)]
type instance DecodedSection UltimateEpistemicInterests = [(Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)]
type instance DecodedSection (Reasons direction defeasible) = [ReasonBlock direction defeasible]

instance InjectiveSection GivenPremises [(Text ⁞ ƮGivenPremise, ProblemJustificationDegree)] where
    decodeSection = simpleParse (many (try p) <* many space <* eof) . unƭ
      where
        p ∷ Parser (Text ⁞ ƮGivenPremise, ProblemJustificationDegree)
        p = do
            spaces
            (t, d) ← many anyChar `precededBy` parserProblemJustificationDegree
            return (ƭ . pack $ t, d)

instance InjectiveSection UltimateEpistemicInterests [(Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)] where
    decodeSection = simpleParse (many (try p) <* many space <* eof) . unƭ
      where
        p ∷ Parser (Text ⁞ ƮUltimateEpistemicInterest, ProblemInterestDegree)
        p = do
            spaces
            (t, d) ← many anyChar `precededBy` parserProblemInterestDegree
            return (ƭ . pack $ t, d)

instance InjectiveSection (Reasons direction defeasible) [ReasonBlock direction defeasible] where
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

data IsAKind kind ⇒ ƮSection kind

class HasSection s where
    section ∷ s → Section

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
newtype LispPositiveDouble = LispPositiveDouble Double
  deriving (Show)

parserLispPositiveDouble ∷ Parser LispPositiveDouble
parserLispPositiveDouble = do
    d ← many space *> manyTill anyChar ((space *> pure ()) <|> eof)
    if null d then
        mzero
    else
        if headEx d == '.' then
            return . LispPositiveDouble . read $ "0" ++ d
        else if headEx d == '-' then
            error "LispPositiveDouble negative number?"
        else
            return . LispPositiveDouble . read $ d

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
data ForwardsReason = ForwardsReason ![Formula] !Formula
  deriving (Show)

data BackwardsReason = BackwardsReason ![Formula] ![Formula] !Formula
  deriving (Show)

--

type Degree = Double
type Strength = Double

data Named r = Named { _value ∷ !r, _namedValue ∷ !Text }
  deriving (Show)
data Degreed r = Degreed Degree r

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

stripMeta ∷ (ProblemReasonName, ForwardsReason, ProblemStrengthDegree) → (ForwardsReason, ProblemStrengthDegree)
stripMeta (_, r, d) = (r, d)

stripMeta' ∷ (ProblemReasonName, BackwardsReason, ProblemStrengthDegree) → (BackwardsReason, ProblemStrengthDegree)
stripMeta' (_, r, d) = (r, d)

pattern BaseProblem p i fpfr fcr bpfr bcr ← Problem n d p i (map stripMeta → fpfr) (map stripMeta → fcr) (map stripMeta' → bpfr) (map stripMeta' → bcr)

problemsM ∷ FilePath ⁞ [ƮProblem] → IO [Problem]
problemsM filePath = do
    combinedProblems ← problemsTextM filePath
    return $ problem <$> problemTexts combinedProblems
  where
    problem ∷ Text ⁞ ƮProblem → Problem
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

        pSTaD :: (HasSection kind) => Text ⁞ ƮSection kind
        pSTaD = problemSectionText afterDescription

fpfrts ∷ ReasonBlock Forwards defeasible → (ProblemReasonName, ForwardsReason, ProblemStrengthDegree)
fpfrts rb = (,,)
    (_rbProblemReasonName rb)
    (fr $ _rbProblemReasonText rb)
    (_rbProblemStrengthDegree rb)
  where
    fr = uncurry ForwardsReason . booyah . unƭ . extractFromProblemReasonTextForwards
    booyah = first (map formulaFromText) . second formulaFromText


bpfrts ∷ forall defeasible. ReasonBlock Backwards defeasible → (ProblemReasonName, BackwardsReason, ProblemStrengthDegree)
bpfrts rb = (,,)
    (_rbProblemReasonName rb)
    (br $ _rbProblemReasonText rb)
    (_rbProblemStrengthDegree rb)
  where
    br = booyah . unƭ . extractFromProblemReasonTextBackwards 

    booyah (fps, bps, c) = BackwardsReason (formulaFromText <$> fps) (formulaFromText <$> bps) (formulaFromText c)
