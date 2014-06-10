{-# LANGUAGE NoImplicitPrelude #-}
--{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Main where

import ClassyPrelude hiding (Text, try)
import Control.Applicative
import Control.Conditional hiding (unlessM)
import Control.Monad
import Data.Char
import Data.Coerce
import Data.Set (Set)
import Data.Tagged
import Data.Text.Internal.Lazy (Text)
import Prelude (read)
import qualified Data.Set as Set
import Safe
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Text.Lazy
import Text.Show.Pretty

--
newtype ProblemsText = ProblemsText Text
    deriving (Show)

ioProblemsTextFromFilePath :: FilePath -> IO ProblemsText
ioProblemsTextFromFilePath = map ProblemsText . readFile

--
newtype ProblemText = ProblemText Text
    deriving (Show)

problemTextsFromProblemsText :: ProblemsText -> [ProblemText]
problemTextsFromProblemsText = map ProblemText . either (error . ppShow) id . runParser (many p) () "" . coerce
    where
        p :: Parser Text
        p = do
            spaces
            string "Problem #"
            pack <$> manyTill anyChar endP

        endP :: Parser ()
        endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

--
newtype AfterProblemNumberText = AfterProblemNumberText Text
    deriving (Show)

newtype ProblemNumber = ProblemNumber Int
    deriving (Show)


--

main :: IO ()
main = do
    combinedProblems <- ioProblemsTextFromFilePath $ fpFromString "Combined-problems"
    putStrLn . pack . ppShow $ combinedProblems
    let ps' :: [ProblemText] = problemTextsFromProblemsText combinedProblems
    let ps = coerce <$> ps'
    sequence_ $ putStrLn . pack . ppShow <$> ps
    sequence_ $ ppn <$> ps
    sequence_ $ ppd . decipher <$> ps
    let reasonTexts = snd . (decipher :: Text -> (ProblemDescription, Text)) . snd . (decipher :: Text -> (ProblemNumber, Text)) <$> ps
    sequence_ $ putStrLn . pack . ppShow . (decipher0 :: Text -> ProblemGivenPremisesText) <$> reasonTexts
    sequence_ $ putStrLn . pack . ppShow . (decipher0 :: Text -> ProblemForwardsPrimaFacieReasonsText) <$> reasonTexts
    sequence_ $ putStrLn . pack . ppShow . (decipherFoo stsBackwardsPrimaFacieReason) <$> reasonTexts

  where
    ppn :: Text -> IO ()
    ppn t = do
        let (pn :: ProblemNumber, t') = decipher t
        putStrLn . pack . ppShow $ pn

    ppd :: (ProblemNumber, Text) -> IO ()
    ppd (_, t) = do
        let (pd :: ProblemDescription, t') = decipher t
        putStrLn . pack . ppShow $ pd


data Section
    =   Section'GivenPremises
    |   Section'UltimateEpistemicInterests
    |   Section'ForwardsPrimaFacieReasons
    |   Section'ForwardsConclusiveReasons
    |   Section'BackwardsPrimaFacieReasons
    |   Section'BackwardsConclusiveReasons
    deriving (Eq, Show)

sectionParser :: Parser Section
sectionParser =
    empty
    <|> string "Given premises:"               `if_then` Section'GivenPremises              
    <|> string "Ultimate epistemic interests:" `if_then` Section'UltimateEpistemicInterests 
    <|> string "FORWARDS PRIMA FACIE REASONS"  `if_then` Section'ForwardsPrimaFacieReasons  
    <|> string "FORWARDS CONCLUSIVE REASONS"   `if_then` Section'ForwardsConclusiveReasons  
    <|> string "BACKWARDS PRIMA FACIE REASONS" `if_then` Section'BackwardsPrimaFacieReasons 
    <|> string "BACKWARDS CONCLUSIVE REASONS"  `if_then` Section'BackwardsConclusiveReasons 
  where
    if_then :: forall a b. Parser a -> b -> Parser b
    if_then p t = pure t <* try p

class Decipherable out where
    decipher :: Text -> (out, Text)

instance Decipherable ProblemNumber where
    decipher = either (error . ppShow) id . runParser p () ""
      where
        p :: Parser (ProblemNumber, Text)
        p = do
            n <- ProblemNumber . read <$> manyTill anyChar (lookAhead . try $ space)
            t <- pack <$> many anyChar
            return (n, t)

newtype ProblemDescription = ProblemDescription Text
    deriving (Show)

instance Decipherable ProblemDescription where
    decipher = either (error . ppShow) id . runParser p () ""
      where
        p :: Parser (ProblemDescription, Text)
        p = do
            _ <- many space
            n <- ProblemDescription . pack <$> manyTill anyChar (lookAhead . try $ many space >> sectionParser)
            t <- pack <$> many anyChar
            return (n, t)

class Decipherable0 a where
    decipher0 :: Text -> a
    decipher0 = either (error . ppShow) id . runParser p () ""
      where
        p :: Parser a
        p = do
            _ <- manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== dv0 (undefined :: a)) sectionParser)
            p' <|> pure ((dc0 :: Text -> a) . pack $ "")
          where
            p' :: Parser a
            p' = do
                guardM (map (== dv0 (undefined :: a)) sectionParser)
                dc0 . pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))
    dv0 :: a -> Section
    dc0 :: Text -> a

newtype ProblemForwardsPrimaFacieReasonsText = ProblemForwardsPrimaFacieReasonsText Text
    deriving (Show)
instance Decipherable0 ProblemForwardsPrimaFacieReasonsText where
    dv0 _ = Section'ForwardsPrimaFacieReasons
    dc0 = ProblemForwardsPrimaFacieReasonsText

data STS output = STS 
    {   stsDV0 :: Section
    ,   stsDC0 :: Text -> output
    }

newtype ProblemBackwardsPrimaFacieReasonsText = ProblemBackwardsPrimaFacieReasonsText Text
    deriving (Show)

stsBackwardsPrimaFacieReason :: STS ProblemBackwardsPrimaFacieReasonsText
stsBackwardsPrimaFacieReason = STS Section'BackwardsPrimaFacieReasons ProblemBackwardsPrimaFacieReasonsText

decipherFoo :: forall a. STS a -> Text -> a
decipherFoo STS {..} = either (error . ppShow) id . runParser p () ""
    where
        p :: Parser a
        p = do
            _ <- manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== stsDV0) sectionParser)
            p' <|> pure (stsDC0 . pack $ "")
          where
            p' :: Parser a
            p' = do
                guardM (map (== stsDV0) sectionParser)
                stsDC0 . pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))




--newtype ReasonText kind = ReasonText Text

--data TaggedBPFR

--data TaggedSTS output = TaggedSTS 
--    {   stsDV0 :: Section
--    ,   stsDC0 :: Text -> ReasonText output
--    }

--newtype ProblemBackwardsPrimaFacieReasonsText = ProblemBackwardsPrimaFacieReasonsText Text
--    deriving (Show)

--taggedStsBackwardsPrimaFacieReason :: STS ProblemBackwardsPrimaFacieReasonsText
--taggedStsBackwardsPrimaFacieReason = STS Section'BackwardsPrimaFacieReasons ProblemBackwardsPrimaFacieReasonsText

--taggedDecipherFoo :: forall a. STS a -> Text -> a
--taggedDecipherFoo STS {..} = either (error . ppShow) id . runParser p () ""
--    where
--        p :: Parser a
--        p = do
--            _ <- manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== stsDV0) sectionParser)
--            p' <|> pure (stsDC0 . pack $ "")
--          where
--            p' :: Parser a
--            p' = do
--                guardM (map (== stsDV0) sectionParser)
--                stsDC0 . pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))







--foo :: Text -> SpecialText Section
--foo = 

--bar :: SpecialText Section -> Text



data SpecialText (v :: Section) = SpecialText Text

decipher1 :: Section -> Text -> SpecialText Section'BackwardsPrimaFacieReasons
decipher1 sec txt = SpecialText $ txt



newtype ProblemGivenPremisesText = ProblemGivenPremisesText Text
    deriving (Show)
instance Decipherable0 ProblemGivenPremisesText where
    dv0 _ = Section'GivenPremises
    dc0 = ProblemGivenPremisesText

eol :: Parser String
eol = map pure lf <|> (try $ liftA2 (:) cr (map pure lf))

lf :: Parser Char
lf = satisfy (== '\n')

cr :: Parser Char
cr = satisfy (== '\r')

withInput :: Monad m => s -> ParsecT s u m a -> ParsecT s u m a
withInput s p = do
    s' <- getInput
    setInput s
    p' <- p
    setInput s'
    return p'

precededBy :: Parser first -> Parser second -> Parser (first, second)
precededBy first second = do
    firstInput <- pack <$> manyTill anyChar (lookAhead . try $ second)
    liftA2 (,) (withInput firstInput first) second

unlessM :: (ToBool bool, MonadPlus m) => m bool -> m a -> m a
unlessM c a = ifM c mzero a



data Problem = Problem
    ProblemNumber
    ProblemDescription
    [ProblemPremise]
    [ProblemInterest]
    [ProblemReason]

newtype Degree = Degree Double
    deriving (Show)

data ProblemPremise = ProblemPremise
    Text
    Degree
    deriving (Show)

data ProblemInterest = ProblemInterest
    Text
    Degree
    deriving (Show)

data ProblemReason = ProblemReason 
    Text 
    Bool 
    Double
    deriving (Show)


data Text'ProblemNumber
data Text'ProblemDescription
data Text'ProblemPremises
data Text'ProblemInterests
data Text'ProblemReasons



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


--data Formula 
--    =   ForAll Var Formula
--    |   Some Var Formula
--    |   Not Formula
--    |   Defeats Formula Formula
--    |   And Formula Formula
--    |   Or Formula Formula
--    |   Implies Formula Formula
--    |   Iff Formula Formula
--    |   Predicate PName [Var]

--data Var 
--    =   Function FunctionName [Var]
--    |   Skolem VName

 
-- :: IO Text'Problems

-- :: Tagged Text'Problems Text -> [Tagged Text'Problem Text]

--problemsFromText :: Text -> [Problem]

--parseProblemFromCombinedProblemsText :: Parser Problem

--parseProblemFromProblemText :: Parser Problem

--problemFromText :: Text -> Problem


--problemNumber `isPrecededBy` problemDescription
--problemDescription `isPrecededBy` 

--class (m' :: Functor f => (* -> *) -> f) where
    
--data Formula = Formula Text -- TODO use a tree rather than a serial structure




--(Section, :: )

-- parser modifications
-- --> new problem
--     set problem number
--     set problem description
--     



-- ParsecT Text 

--defineSection :: Parser before -> 


--manyTill' :: Parser a -> Parser end -> Parser ([a], end)
--manyTill' a end = do 
--    a' <- manyTill a (lookAhead . try $ end)
--    end' <- end
--    return (a', end')



--------------

--data CombinedProblemText

--newtype CombinedProblemText = CombinedProblemText Text

-- :: Parser ProblemText

--TProblems -> [TProblem]

--TProblem -> (TProblem1, TProblem2, TProblem3)
--do 
--    _ <- string "Problem #"
--    problemNumberText <- manyTill anyChar space
--    spaces
--    descriptionText <- manyTill anyChar (lookAhead . try $ sectionTitle)

--data Marker


{-
What if the user state stores a map of markers?
-}



--TProblem1 -> (Number, Description)

--TProblem2 -> (SSectionType, TSection)

-- CombinedProblems is Text, known to be convertible to [Problem], where Problem is "structured"

-- CombinedProblems -> [TProblem]

--newtype P = P Text

--ps :: Tagged CombinedProblems Text -> [P]
--ps :: CombinedProblemsText -> [P]

--    :: Parser [P]

--        :: Parser P

--rP :: Parser P

--newtype P1 = P1 Text
--newtype P2 = P2 Text

--p12 :: P -> (P1, P2)
--    :: Parser (P1, P2)

-- sections divided by "Problem #"
-- divide into number & description vs other sections(:)
-- 

--data ProblemToken 
--    =   TProblemNumber Int
--    |   TDescription Text
--    |   TSection SectionTitle Text

--ParsecT Text 

--data SectionToken
--    =   

--TSectionText Text -> 


--ParsecT Text ()

---- Text --> 

-- :: Text -> [ProblemText]

--data ProblemText 
--    =   ProblemText'ProblemNumber Text
--    |   ProblemText'ProblemDescription Text
--    |   ProblemText'PremiseText Text

    
    
    

--[ProblemText] -> [[ProblemText]]







--data ProblemParserState where
--    Start :: ProblemParserState 


--newtype IsDefeasible = IsDefeasible Bool

--data Premise
--data Interest
--data Reason direction 



--newtype 

--data IsProblemNumber

--Tagged IsProblemNumber 

--data IsProblemDescription
--data 


--newtype TextOfProblemNumber







-----------

--type value ::: tag = Tagged tag value

--newtype 

--data ProblemTexts = ProblemTexts 
--    {   ptNumber :: Text
--    ,   ptDescription :: Text
--    ,   ptGivenPremises :: Text
--    ,   ptUEI :: Text
--    ,   ptFPFReasons :: Text
--    ,   ptFCReasons :: Text
--    ,   ptBPFReasons :: Text
--    ,   ptBCReasons :: Text
--    }

-- :: Text -> ProblemNumber

-- :: Text -> ProblemDescription
-- :: Text -> [GivenPremisesText]

--GivenPremisesText -> ()

--GivenPremisesText -> 



--data ProblemSchemaText = 
--    PSTProblemNumber
--    PST

--data CombinedProblemsText
--data 

-- :: Text -> CombinedProblemsText

--CombinedProblemsText -> (ProblemNumberText, ProblemDescriptionText, GivenPremisesText, UltimateEpistemicInterestsText, OtherText)

--PrefixedSectionsText -> GivenPremisesText
--PrefixedSectionsText -> UltimateEpistemicInterestsText

--GivenPremisesText -> GivenPremiseText

--GivenPremiseText -> (FormulaText, DegreeText)

--data Problem = Problem 
--    ProblemNumber 
--    ProblemDescription 
--    [Text]
--    [Text]
--    [Text]
--    [Text]
--    [Text]
--    [Text]



--BlockParser

--char :: ParsecT Text Text Identity Char
--char = do
--    <- P.char


---- passThrough x parses x, returning the 
--passThrough :: Parser a -> Parser Text
--passThrough a = do

--problemsParser :: Parser [Problem]
--problemsParser = do
--    sectionsBetween (string "Problem #")
--    problemParser


--problemParser :: Parser Problem
--problemParser = do
--    string "Problem #"
--    endingWith (eof <|> string "Problem #") $ do
--        problemNumber <- endingWith space parseProblemNumber
--        skip spaces
--        problemDescription <- endingWith parseAnySectionTitle parseDescription
--        premiseSection <- lookAhead $ between 
--        premiseDeclarations <- parseWith premiseSection $ many parseAnyDegreedDeclaration
--        return $
--            ProblemNumber 
--                problemNumber 
--                problemDescription
--                premiseDeclarations

--type PhaseStream phase = Tagged phase Text



--newtype PhaseStream phase = PhaseStream Text
--    deriving (Show)

--data Phase'CombinedProblems



--combinedProblemsFileReader :: IO (PhaseStream Phase'CombinedProblems)
--combinedProblemsFileReader = PhaseStream <$> readFile (fpFromString "Combined-problems")

--class PhaseParser output where 
--    type InputPhase output :: *
--    phaseParser :: Parser output

--runPhase :: (PhaseParser output) => String -> PhaseStream (InputPhase output) -> output
--runPhase name = either (error . ppShow) id . runParser phaseParser () name . coerce

--data Phase'FromEndOfLabelOfProblemNumber

--instance PhaseParser [PhaseStream Phase'FromEndOfLabelOfProblemNumber] where
--    type InputPhase [PhaseStream Phase'FromEndOfLabelOfProblemNumber] = Phase'CombinedProblems
--    phaseParser = many pp
--      where
--        pp :: Parser (PhaseStream Phase'FromEndOfLabelOfProblemNumber)
--        pp = PhaseStream . pack <$> p
--          where 
--            p :: Parser String
--            p = do
--                _ <- many space
--                _ <- string "Problem #"
--                manyTill anyChar $ 
--                    eof <|> (pure () <* lookAhead (try $ string "Problem #"))

--newtype ProblemNumber = ProblemNumber Int
--    deriving (Show)

--data Phase'FromEndOfValueOfProblemNumber

--instance PhaseParser (ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber) where
--    type InputPhase (ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber) = Phase'FromEndOfLabelOfProblemNumber
--    phaseParser = do
--        pn <- manyTill anyChar $ lookAhead space
--        rest <- getInput 
--        return (ProblemNumber . readNote "ProblemNumber" $ pn, PhaseStream rest)

--newtype ProblemDescription = ProblemDescription Text
--    deriving (Show)

--data Phase'FromBeginningOfProblemDescriptionToBeginningOfSections
--data Phase'FromBeginningOfSections

--instance PhaseParser (PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections) where
--    type InputPhase (PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections) = Phase'FromEndOfValueOfProblemNumber
--    phaseParser = do
--        desc <- manyTill anyChar $ lookAhead . try $ eol >> many space >> sectionTitleParser
--        rest <- getInput
--        return (PhaseStream . pack $ desc, PhaseStream rest)

--instance PhaseParser ProblemDescription where
--    type InputPhase ProblemDescription = Phase'FromBeginningOfProblemDescriptionToBeginningOfSections
--    phaseParser = ProblemDescription . pack <$> (many space *> manyTill anyChar (lookAhead . try $ many space >> eof))

--instance PhaseParser [SectionTitle] where
--    type InputPhase [SectionTitle] = Phase'FromBeginningOfSections
--    phaseParser = many (try $ snd <$> manyTill' anyChar sectionTitleParser)

---- |  TaggedSectionTitle
--class TaggedSectionTitle output where
--    taggedSectionTitle :: Tagged output SectionTitle

--data                           Phase'Section'GivenPremises
--instance TaggedSectionTitle    Phase'Section'GivenPremises where
--    taggedSectionTitle = Tagged SectionTitle'GivenPremises

--data                           Phase'Section'UltimateEpistemicInterests
--instance TaggedSectionTitle    Phase'Section'UltimateEpistemicInterests where
--    taggedSectionTitle = Tagged SectionTitle'UltimateEpistemicInterests

--data                           Phase'Section'ForwardsPrimaFacieReasons
--instance TaggedSectionTitle    Phase'Section'ForwardsPrimaFacieReasons where
--    taggedSectionTitle = Tagged SectionTitle'ForwardsPrimaFacieReasons

--data                           Phase'Section'ForwardsConclusiveReasons
--instance TaggedSectionTitle    Phase'Section'ForwardsConclusiveReasons where
--    taggedSectionTitle = Tagged SectionTitle'ForwardsConclusiveReasons

--data                           Phase'Section'BackwardsPrimaFacieReasons
--instance TaggedSectionTitle    Phase'Section'BackwardsPrimaFacieReasons where
--    taggedSectionTitle = Tagged SectionTitle'BackwardsPrimaFacieReasons

--data                           Phase'Section'BackwardsConclusiveReasons
--instance TaggedSectionTitle    Phase'Section'BackwardsConclusiveReasons where
--    taggedSectionTitle = Tagged SectionTitle'BackwardsConclusiveReasons
----


--instance TaggedSectionTitle output => PhaseParser (PhaseStream output) where
--    type InputPhase (PhaseStream output) = Phase'FromBeginningOfSections
--    phaseParser = do
--        availableTitles :: [SectionTitle] <- lookAhead phaseParser
--        let sectionTitle = unTagged (taggedSectionTitle :: Tagged output SectionTitle)
--        if sectionTitle `elem` availableTitles then do
--            _ <- manyTill' anyChar (guardM $ (== sectionTitle) <$> sectionTitleParser)
--            _ <- many space
--            (s, _) <- manyTill' anyChar (eof <|> (guardM $ (/= sectionTitle) <$> sectionTitleParser))
--            return $ PhaseStream . pack $ s
--        else
--            return $ PhaseStream . pack $ ""


----data Premise = Premise Formula Degree

----data Phase'Single'GivenPremises

----instance PhaseParser Phase'Single'GivenPremises where
----    type InputPhase Phase'Section'Single'GivenPremises = Phase'Section'GivenPremises
----    phaseParser = do
----        manyTill

----instance PhaseParser (Premise, Phase'Section'GivenPremises) where
----    type InputPhase Premises = Phase'Section'GivenPremises
----    phaseParser = do 

----        Premise <$> formulaParser <*>  (Premises . pack . fst <$> manyTill' anyChar (many space >> eof))

----parallelParse :: Parse a -> Parse b -> Parser (Maybe a, Maybe b)
----parallelParse a b = do

--newtype Degree = Degree Double
--    deriving (Show)

--degreeParser :: Parser Degree
--degreeParser = Degree . read <$> (degreeLabelParser *> many space *> string "=" *> many space *> manyTill anyChar space)
--  where
--    degreeLabelParser = try (string "justification") <|> try (string "strength") <|> string "interest"

--data Phase'Formula

--instance PhaseParser [(PhaseStream Phase'Formula, Degree)] where
--    type InputPhase [(PhaseStream Phase'Formula, Degree)] = Phase'Section'GivenPremises
--    phaseParser = many onePremise
--      where
--        onePremise :: Parser (PhaseStream Phase'Formula, Degree)
--        onePremise = do
--            (f, d) <- many anyChar `followedBy` (many space *> degreeParser <* many space)
--            return (PhaseStream . pack $ f, d)


--newtype GivenPremises = GivenPremises Text
--    deriving (Show)

--instance PhaseParser GivenPremises where
--    type InputPhase GivenPremises = Phase'Section'GivenPremises
--    phaseParser = GivenPremises . pack <$> many anyChar


--newtype BackwardsPrimaFacieReasons = BackwardsPrimaFacieReasons Text
--    deriving (Show)

--instance PhaseParser BackwardsPrimaFacieReasons where
--    type InputPhase BackwardsPrimaFacieReasons = Phase'Section'BackwardsPrimaFacieReasons
--    phaseParser = BackwardsPrimaFacieReasons . pack <$> many anyChar

--main :: IO ()
--main = do 
--    combinedProblems <- combinedProblemsFileReader
--    let p1  :: [PhaseStream Phase'FromEndOfLabelOfProblemNumber] = runPhase "1" combinedProblems
--    let p2s :: [(ProblemNumber, PhaseStream Phase'FromEndOfValueOfProblemNumber)] = runPhase "2" <$> p1
--    let p3s :: [(PhaseStream Phase'FromBeginningOfProblemDescriptionToBeginningOfSections, PhaseStream Phase'FromBeginningOfSections)] = runPhase "3" . snd <$> p2s
--    --let p4s :: [PhaseStream Phase'Section'GivenPremises] = runPhase "4" . snd <$> p3s
--    let gps :: [[GivenPremise]] = runPhase "5" <$> p4s
--    --let p5s :: [GivenPremises] = runPhase "5" <$> p4s
--    let p6s :: [PhaseStream Phase'Section'BackwardsPrimaFacieReasons] = runPhase "6" . snd <$> p3s
--    let p7s :: [BackwardsPrimaFacieReasons] = runPhase "7" <$> p6s

--    let ns = map fst p2s
--    let ds :: [ProblemDescription] = runPhase "descriptions" <$> map fst p3s

--    --sequence_ $ putStrLn . pack . ppShow <$> ns
--    --sequence_ $ putStrLn . pack . ppShow <$> ds
--    --sequence_ $ putStrLn . pack . ppShow <$> p5s
--    sequence_ $ putStrLn . pack . ppShow <$> p7s
--    sequence_ $ putStrLn . pack . ppShow <$> gps
