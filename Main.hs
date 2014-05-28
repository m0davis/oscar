{-# LANGUAGE NoImplicitPrelude #-}
--{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import ClassyPrelude hiding (Text, try)
import Prelude (read)

import Control.Conditional hiding (unlessM)
import Control.Monad
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Char

import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Text.Lazy

import Data.Text.Internal.Lazy (Text)
import Data.Coerce

import Text.Show.Pretty

import Safe

import Control.Applicative

--import Debug.Trace

--data Problem = Problem
--    ProblemNumber
--    ProblemDescription
--    (Set Premise)
--    --(Set Interest)
--    --(Set ForwardsPrimaFacieReason)
--    --(Set ForwardsConclusiveReason)
--    --(Set BackwardsPrimaFacieReason)
--    --(Set BackwardsConclusiveReason)
--    deriving (Eq, Ord, Show, Read)

--newtype ProblemNumber = ProblemNumber Int
--    deriving (Eq, Ord, Show, Read)

--newtype ProblemDescription = ProblemDescription Text
--    deriving (Eq, Ord, Show, Read)

--newtype Degree = Degree Double
--    deriving (Eq, Ord, Show, Read)

--newtype Formula = Formula Text
--    deriving (Eq, Ord, Show, Read)

--data Premise = Premise Formula Degree
--    deriving (Eq, Ord, Show, Read)

--data Interest = Interest Formula Degree
--    deriving (Eq, Ord, Show, Read)

--newtype Variable = Variable Text
--    deriving (Eq, Ord, Show, Read)

--data ForwardsPrimaFacieReason = ForwardsPrimaFacieReason (Set Formula) Formula (Set Variable) Degree
--    deriving (Eq, Ord, Show, Read)

--data ForwardsConclusiveReason = ForwardsConclusiveReason (Set Formula) Formula (Set Variable)
--    deriving (Eq, Ord, Show, Read)

--data BackwardsPrimaFacieReason = BackwardsPrimaFacieReason (Set Formula) (Set Formula) Formula (Set Variable) Degree
--    deriving (Eq, Ord, Show, Read)

--data BackwardsConclusiveReason = BackwardsConclusiveReason (Set Formula) (Set Formula) Formula (Set Variable)
--    deriving (Eq, Ord, Show, Read)

--skipSpacesPastEndOfLine :: Parser ()
--skipSpacesPastEndOfLine = do
--    manyTill space (lookAhead $ eol)

----    skipSpaceChars
----    skipNewline
----    return ()

--skipSpaceChars :: Parser ()
--skipSpaceChars = skipMany (satisfy (== ' '))

--skipNewline :: Parser ()
--skipNewline = skipNewlineLF <|> skipNewlineCRLF

--skipNewlineLF :: Parser ()
--skipNewlineLF = satisfy (== '\n') *> pure ()

--skipNewlineCRLF :: Parser ()
--skipNewlineCRLF = satisfy (== '\r') *> satisfy (== '\n') *> pure ()

--skipString :: String -> Parser ()
--skipString s = string s *> pure ()

--emptyLine :: Parser ()
--emptyLine = do
--    skipSpaceChars
--    skipNewline
--    return ()

--debugShowInput = getInput >>= traceShowM . take 100

---- starts from the beginning of the "Problem #" line
---- ends after the newline
--problemNumberLine :: Parser ProblemNumber
--problemNumberLine = do
--    skipString "Problem #" *> (ProblemNumber . read . (\x -> [x]) <$> {-many-} (satisfy isDigit)) <* emptyLine

---- starts from after the newline after the "Problem #" line
---- ends after the newline right before the header line for given premises
--problemDescription :: Parser ProblemDescription
--problemDescription = do
--    ProblemDescription . pack <$> 
--        manyTill anyChar
--            (try . lookAhead $ many emptyLine >> headerLine "Given premises:")

--prFormula :: Parser Formula
--prFormula = Formula . pack <$> many anyChar

--prDegree :: Parser Degree
--prDegree = Degree . read <$> manyTill anyChar (try . lookAhead $ emptyLine)

--unlessM :: (ToBool bool, MonadPlus m) => m bool -> m a -> m a
--unlessM c a = ifM c mzero a

--premiseParser :: Parser Premise
--premiseParser = do
--    unlessM (isAhead $ skipString "Ultimate epistemic interests:" >> emptyLine) $ do
--        (f, (_, d)) <- 
--            between_ng
--                skipSpaceChars 
--                (prFormula) 
--                (skipSpaceChars *> skipString "justification" *> skipSpaceChars *> skipString "=" *> skipSpaceChars *> 
--                    prDegree 
--                    <* (emptyLine))
--        return $ Premise f d

--isAhead :: Parser a -> Parser Bool
--isAhead p = (lookAhead p *> pure True) <|> pure False

--between_ng :: Parser open -> Parser between -> Parser close -> Parser (between, (open, close))
--between_ng o b c = do
--    o' <- o
--    interior <- manyTill anyChar (try . lookAhead $ c)
--    let (Right b') = runP b () "" (pack interior)
--    c' <- c
--    return (b', (o', c'))

--newtype ProblemBlock = ProblemBlock Text

--problemDelimiter :: Parser ()
--problemDelimiter = try $ skipSpaceChars >> skipString "Problem #"

---- first scan through to collect the tokens

--data ProblemToken
--    =   PTContent
--    |   PTProblemNumber 
--    |   PTGivenPremises
--    |   PTUltimateEpistemicInterests
--    |   PTForwardsPrimaFacieReasons
--    |   PTForwardsConclusiveReasons
--    |   PTBackwardsPrimaFacieReasons
--    |   PTBackwardsConclusiveReasons

--data 

--data ProblemState
--    =   PSTop
--    |   PS

--"Problem #"
--"Given premises:"
--problemsParser :: ParsecT [Problem]
--problemsParser = do
--    anyWhitespace

--rsProblemNumber :: Parser ProblemNumber
--rsProblemNumber = do

--problemParser :: Parser Problem
--premiseParser = do
--    n <- problemNumber
--    d <- problemDescription
--    problemLabel



---- how about a backtracking parser

--ignore 
--skip beginning of "Problem #"
--look for the NEXT "Problem #" or eof
--collect from those two endpoints --> Problem parser

--Parser begin -> Parser end -> Parser within -> Parser within

--Within a "Problem #..."
--ignore "Problem #"
--collect from there to spaceOrEol --> Problem Number parser
--skip all that
--collect from there to beginning of Given premises: --> Problem description parser
--skip all that
--problemNumberLabel :: Parser ()
--givenPremisesLabel :: Parser ()
--anyWhitespace :: Parser ()
--restOfLine :: Parser ()
--formula :: Parser Formula
--degreeOfJustification :: Parser Degree
--ultimateEpistemicInterestsLabel :: Parser ()
--degreeOfInterest :: Parser Degree
--forwardsPrimaFacieReasonsLabel :: Parser ()
--backwardsPrimaFacieReasonsLabel :: Parser ()
--forwardsConclusiveFacieReasonsLabel :: Parser ()
--forwardsConclusiveFacieReasonsLabel :: Parser ()
--anyReasonsLabel :: Parser ()
--variables :: Parser Variables



--tokenize1 :: Parser [Text]
--tokenize1 = do
--    ignore *> captureBefore  <* 
--    beginToken *> many 
--  where
--    ignore :: Parser 
--    beginToken :: Parser ()
--    beginToken = string 
--    Parser beginEra -> 
--    Parser endEra -> 
--    [Text]



--Text -> 

--_ <- ignorable

---- grammar definition
--_ <- many (space <|> newline)
--_ <- string "Problem #"
--(problemNumber, _) <- integer `priorTo` (many space >> newline)
--_ <- newline
--(problemDescription, _) <- 
--    many anyChar 
--        `priorTo` 
--            (newline >> many space >> string "Given premises:" >> many space >> newline)
--premises <- many . try $ do
--    many space
--    (formula, degree) <- 
--        parseFormula
--            `priorTo` 
--                (many space >> string "justification" >> many space >> string "=" >> many space >> (double `priorTo` (many space >> newline)))
--    return $ Premise premiseFormula premiseDegree
--ultimateEpistemicInterests <- do 
--    many (space <|> newline) >> string "Ultimate epistemic interests:"
--    (u)
--    ultimateEpistemicInterestsParser `priorTo` reasonsParser

--(forwardsPrimaFacieReasons, backwardsPrimaFacieReasons, forwardsConclusiveReasons, backwardsConclusiveReasons)

--reasonsParser = do

--reasonSectionParser :: Parser (Section, )



--ultimateEpistemicInterests <-




---- < >"Problem #"

---- a Problem Number is...

--ParsecT [ProblemToken] m ProblemToken

--sp :: ParsecT  ProblemSection
--sp = do
--    if lookAhead ""

---- run 'a' within boundaries defined by 'sep', which are not(?) included in the subtext
--Parser sep -> Parser a -> Parser [a]

--ParsecT s u m sep 

--problemParser :: Parser Problem
--problemParser = do
--    debugShowInput
--    fst <$> between_ng
--        (pure ())
--        (do 
--            debugShowInput
--            traceM "1"
--            many emptyLine
--            traceM "2"
--            pn <- problemNumberLine
--            traceM "3"
--            many emptyLine
--            traceM "4"
--            desc <- problemDescription
--            traceM "5"
--            many emptyLine
--            traceM "6"
--            (prems, _) <- 
--                between_ng 
--                    (headerLine "Given premises:")
--                    (Set.fromList <$> many premiseParser)
--                    (headerLine "Ultimate epistemic interests:")
--            traceM "7"
--            return $ Problem pn desc prems
--            )
--        (try . lookAhead $ string "Problem #")

--headerLine :: String -> Parser ()
--headerLine s = do
--    skipSpaceChars
--    skipString s
--    skipSpaceChars
--    skipNewline

--skipToProblemStart :: Parser ()
--skipToProblemStart = do
--    manyTill anyChar (try . lookAhead $ string "Problem #") *> pure ()

------------------

------------------







--    runParser 
--  where 

--ProblemBlock -> (ProblemNumberBlock, ProblemDescriptionBlock, [PremiseText], [UEInterestText], ReasonsText)

--ProblmNumberBlock -> ProblemNumber

--PremiseText 

--ReasonsBlock -> (ForwardsPrimaFacieReasonsBlock, BackwardsPrimaFacieReasonsBlock, ForwardsConclusiveReasonsBlock, BackwardsConclusiveReasonsBlock)

--ForwardsPrimaFacieReasonsBlock -> ReasonBlock

--ReasonBlock -> ForwardsPrimaFacieReason

--ReasonBlock -> BackwardsPrimaFacieReason

--ReasonBlock -> ForwardsConclusiveReason

--ReasonBlock -> BackwardsConclusiveReason



--problemsParser :: Parser [ProblemText]
--problemsParser = do
--    many space
--    manyTill 


eol :: Parser String
eol = map pure lf <|> (try $ liftA2 (:) cr (map pure lf))

lf :: Parser Char
lf = satisfy (== '\n')

cr :: Parser Char
cr = satisfy (== '\r')

-----------

newtype PhaseStream phase = PhaseStream Text
    deriving (Show)

data Phase'CombinedProblems

combinedProblemsFileReader :: IO (PhaseStream Phase'CombinedProblems)
combinedProblemsFileReader = PhaseStream <$> readFile (fpFromString "Combined-problems")

class PhaseParser output where 
    type InputPhase output :: *
    phaseParser :: Parser output

runPhase :: (PhaseParser output) => String -> PhaseStream (InputPhase output) -> output
runPhase name = either (error . ppShow) id . runParser phaseParser () name . coerce

data Phase'FromEndOfLabelOfProblemNumber

instance PhaseParser [PhaseStream Phase'FromEndOfLabelOfProblemNumber] where
    type InputPhase [PhaseStream Phase'FromEndOfLabelOfProblemNumber] = Phase'CombinedProblems
    phaseParser = many pp
      where
        pp :: Parser (PhaseStream Phase'FromEndOfLabelOfProblemNumber)
        pp = PhaseStream . pack <$> p
          where 
            p :: Parser String
            p = do
                _ <- many space
                _ <- string "Problem #"
                manyTill anyChar $ 
                    eof <|> (pure () <* lookAhead (try $ string "Problem #"))

newtype ProblemNumber = ProblemNumber Int
    deriving (Show)

data Phase'FromEndOfValueOfProblemNumber

instance PhaseParser (ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber) where
    type InputPhase (ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber) = Phase'FromEndOfLabelOfProblemNumber
    phaseParser = do
        pn <- manyTill anyChar $ lookAhead space
        rest <- getInput 
        return (ProblemNumber . readNote "ProblemNumber" $ pn, PhaseStream rest)

data SectionTitle
    =   SectionTitleGivenPremises
    |   SectionTitleUltimateEpistemicInterests
    |   SectionTitleForwardsPrimaFacieReasons
    |   SectionTitleForwardsConclusiveReasons
    |   SectionTitleBackwardsPrimaFacieReasons
    |   SectionTitleBackwardsConclusiveReasons
    deriving (Eq)

sectionTitleParser :: Parser SectionTitle
sectionTitleParser = do
    empty
    <|> (pure SectionTitleGivenPremises              <* try (string "Given premises:"))
    <|> (pure SectionTitleUltimateEpistemicInterests <* try (string "Ultimate epistemic interests:"))
    <|> (pure SectionTitleForwardsPrimaFacieReasons  <* try (string "FORWARDS PRIMA FACIE REASONS"))
    <|> (pure SectionTitleForwardsConclusiveReasons  <* try (string "FORWARDS CONCLUSIVE REASONS"))
    <|> (pure SectionTitleBackwardsPrimaFacieReasons <* try (string "BACKWARDS PRIMA FACIE REASONS"))
    <|> (pure SectionTitleBackwardsConclusiveReasons <* try (string "BACKWARDS CONCLUSIVE REASONS"))

newtype ProblemDescription = ProblemDescription Text
    deriving (Show)

data Phase'FromBeginningOfProblemDescriptionToBeginningOfSections
data Phase'FromBeginningOfSections

instance PhaseParser (PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections) where
    type InputPhase (PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections) = Phase'FromEndOfValueOfProblemNumber
    phaseParser = do
        desc <- manyTill anyChar $ lookAhead . try $ eol >> many space >> sectionTitleParser
        rest <- getInput
        return (PhaseStream . pack $ desc, PhaseStream rest)

instance PhaseParser ProblemDescription where
    type InputPhase ProblemDescription = Phase'FromBeginningOfProblemDescriptionToBeginningOfSections
    phaseParser = ProblemDescription . pack <$> (many space *> manyTill anyChar (lookAhead . try $ many space >> eof))

data Phase'GivenPremisesSection

instance PhaseParser (PhaseStream Phase'GivenPremisesSection) where
    type InputPhase (PhaseStream Phase'GivenPremisesSection) = Phase'FromBeginningOfSections
    phaseParser = do
        _ <- manyTill anyChar $ lookAhead . try . guardM $ (== SectionTitleGivenPremises) <$> sectionTitleParser
        s <- manyTill anyChar $ lookAhead . try . guardM $ (/= SectionTitleGivenPremises) <$> sectionTitleParser
        return $ PhaseStream . pack $ s

main :: IO ()
main = do 
    combinedProblems <- combinedProblemsFileReader
    let p1  :: [PhaseStream Phase'FromEndOfLabelOfProblemNumber] = runPhase "1" combinedProblems
    let p2s :: [(ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber)] = runPhase "2" <$> p1
    let p3s :: [(PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections)] = runPhase "3" . snd <$> p2s
    let p4s :: [PhaseStream Phase'GivenPremisesSection] = runPhase "4" . snd <$> p3s

    let ns = map fst p2s
    let ds :: [ProblemDescription] = runPhase "descriptions" <$> map fst p3s

    sequence_ $ putStrLn . pack . ppShow <$> ns
    sequence_ $ putStrLn . pack . ppShow <$> ds
