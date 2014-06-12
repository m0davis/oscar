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
{-# LANGUAGE FlexibleContexts #-}

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
import Text.Show.Pretty (ppShow)
import Numeric (readFloat, readSigned)

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

problemNumberAndAfterProblemNumberTextFromProblemText :: ProblemText -> (ProblemNumber, AfterProblemNumberText)
problemNumberAndAfterProblemNumberTextFromProblemText = either (error . ppShow) id . runParser p () "" . coerce
    where
        p :: Parser (ProblemNumber, AfterProblemNumberText)
        p = do
            n <- ProblemNumber . read <$> manyTill anyChar (lookAhead . try $ space)
            t <- pack <$> many anyChar
            return (n, AfterProblemNumberText t)

--
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

--
newtype AfterProblemDescriptionText = AfterProblemDescriptionText Text
    deriving (Show)

newtype ProblemDescription = ProblemDescription Text
    deriving (Show)

problemDescriptionAndAfterProblemDescriptionTextFromAfterProblemNumberText :: AfterProblemNumberText -> (ProblemDescription, AfterProblemDescriptionText)
problemDescriptionAndAfterProblemDescriptionTextFromAfterProblemNumberText = either (error . ppShow) id . runParser p () "" . coerce
    where
        p :: Parser (ProblemDescription, AfterProblemDescriptionText)
        p = do
            _ <- many space
            n <- ProblemDescription . pack <$> manyTill anyChar (lookAhead . try $ many space >> sectionParser)
            t <- pack <$> many anyChar
            return (n, AfterProblemDescriptionText t)

--
newtype ProblemGivenPremisesText = ProblemGivenPremisesText Text
    deriving (Show)

newtype ProblemUltimateEpistemicInterestsText = ProblemUltimateEpistemicInterestsText Text
    deriving (Show)

newtype ProblemForwardsPrimaFacieReasonsText = ProblemForwardsPrimaFacieReasonsText Text
    deriving (Show)

newtype ProblemForwardsConclusiveReasonsText = ProblemForwardsConclusiveReasonsText Text
    deriving (Show)

newtype ProblemBackwardsPrimaFacieReasonsText = ProblemBackwardsPrimaFacieReasonsText Text
    deriving (Show)

newtype ProblemBackwardsConclusiveReasonsText = ProblemBackwardsConclusiveReasonsText Text
    deriving (Show)

data SectionTextFromAfterProblemDescriptionText output = SectionTextFromAfterProblemDescriptionText
    {   _section :: Section
    ,   _pack :: Text -> output
    }

givenPremises :: SectionTextFromAfterProblemDescriptionText ProblemGivenPremisesText
givenPremises = SectionTextFromAfterProblemDescriptionText Section'GivenPremises ProblemGivenPremisesText

ultimateEpistemicInterests :: SectionTextFromAfterProblemDescriptionText ProblemUltimateEpistemicInterestsText
ultimateEpistemicInterests = SectionTextFromAfterProblemDescriptionText Section'UltimateEpistemicInterests ProblemUltimateEpistemicInterestsText

forwardsPrimaFacieReasons :: SectionTextFromAfterProblemDescriptionText ProblemForwardsPrimaFacieReasonsText
forwardsPrimaFacieReasons = SectionTextFromAfterProblemDescriptionText Section'ForwardsPrimaFacieReasons ProblemForwardsPrimaFacieReasonsText

forwardsConclusiveReasons :: SectionTextFromAfterProblemDescriptionText ProblemForwardsConclusiveReasonsText
forwardsConclusiveReasons = SectionTextFromAfterProblemDescriptionText Section'ForwardsConclusiveReasons ProblemForwardsConclusiveReasonsText

backwardsPrimaFacieReasons :: SectionTextFromAfterProblemDescriptionText ProblemBackwardsPrimaFacieReasonsText
backwardsPrimaFacieReasons = SectionTextFromAfterProblemDescriptionText Section'BackwardsPrimaFacieReasons ProblemBackwardsPrimaFacieReasonsText

backwardsConclusiveReasons :: SectionTextFromAfterProblemDescriptionText ProblemBackwardsConclusiveReasonsText
backwardsConclusiveReasons = SectionTextFromAfterProblemDescriptionText Section'BackwardsConclusiveReasons ProblemBackwardsConclusiveReasonsText

sectionTextFromAfterProblemDescriptionText :: forall output. SectionTextFromAfterProblemDescriptionText output -> AfterProblemDescriptionText -> output
sectionTextFromAfterProblemDescriptionText SectionTextFromAfterProblemDescriptionText {..} = either (error . ppShow) id . runParser p () "" . coerce
    where
        p :: Parser output
        p = do
            _ <- manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== _section) sectionParser)
            p' <|> pure (_pack . pack $ "")
          where
            p' :: Parser output
            p' = do
                guardM (map (== _section) sectionParser)
                _pack . pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

--
newtype LispPositiveDouble = LispPositiveDouble Double
    deriving (Show)

parserLispPositiveDouble :: Parser LispPositiveDouble
parserLispPositiveDouble = do
    d <- many space *> manyTill anyChar ((space *> pure ()) <|> eof)
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

parserProblemJustificationDegree :: Parser ProblemJustificationDegree
parserProblemJustificationDegree = ProblemJustificationDegree <$> (many space *> string "justification" *> many space *> char '=' *> parserLispPositiveDouble)

--
newtype ProblemGivenPremiseText = ProblemGivenPremiseText Text
    deriving (Show)

problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText :: ProblemGivenPremisesText -> [(ProblemGivenPremiseText, ProblemJustificationDegree)]
problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
    where
        p :: Parser (ProblemGivenPremiseText, ProblemJustificationDegree)
        p = do
            many space
            (t, d) <- many anyChar `precededBy` parserProblemJustificationDegree
            return (ProblemGivenPremiseText . pack $ t, d)

--
newtype ProblemInterestDegree = ProblemInterestDegree LispPositiveDouble
    deriving (Show)

parserProblemInterestDegree :: Parser ProblemInterestDegree
parserProblemInterestDegree = ProblemInterestDegree <$> (many space *> string "interest" *> many space *> char '=' *> parserLispPositiveDouble)

--
newtype ProblemUltimateEpistemicInterestText = ProblemUltimateEpistemicInterestText Text
    deriving (Show)

problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText :: ProblemUltimateEpistemicInterestsText -> [(ProblemUltimateEpistemicInterestText, ProblemInterestDegree)]
problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
    where
        p :: Parser (ProblemUltimateEpistemicInterestText, ProblemInterestDegree)
        p = do
            many space
            (t, d) <- many anyChar `precededBy` parserProblemInterestDegree
            return (ProblemUltimateEpistemicInterestText . pack $ t, d)

--
newtype ProblemVariablesText = ProblemVariablesText Text
    deriving (Show)

parserProblemVariablesText :: Parser ProblemVariablesText
parserProblemVariablesText = ProblemVariablesText . pack <$> (option "" . try $ many space *> string "variables" *> many space *> char '=' *> many space *> char '{' *> manyTill anyChar (lookAhead . try $ char '}') <* char '}')

--
newtype ProblemStrengthDegree = ProblemStrengthDegree LispPositiveDouble
    deriving (Show)

parserProblemStrengthDegree :: Parser ProblemStrengthDegree
parserProblemStrengthDegree = ProblemStrengthDegree <$> (many space *> string "strength" *> many space *> char '=' *> parserLispPositiveDouble)

--
newtype ProblemReasonName = ProblemReasonName Text
    deriving (Show)

parserProblemReasonName :: Parser ProblemReasonName
parserProblemReasonName = ProblemReasonName . pack <$> (many space *> manyTill anyChar (lookAhead . try $ char ':') <* char ':')

--
newtype ProblemForwardsPrimaFacieReasonText = ProblemForwardsPrimaFacieReasonText Text
    deriving (Show)

newtype ProblemForwardsConclusiveReasonText = ProblemForwardsConclusiveReasonText Text
    deriving (Show)

newtype ProblemBackwardsPrimaFacieReasonText = ProblemBackwardsPrimaFacieReasonText Text
    deriving (Show)

newtype ProblemBackwardsConclusiveReasonText = ProblemBackwardsConclusiveReasonText Text
    deriving (Show)









class (Coercible input Text, Coercible Text output) => CoercibleForwards input output | input -> output where

instance CoercibleForwards ProblemForwardsPrimaFacieReasonsText ProblemForwardsPrimaFacieReasonText

instance CoercibleForwards ProblemForwardsConclusiveReasonsText ProblemForwardsConclusiveReasonText

instance CoercibleForwards ProblemBackwardsPrimaFacieReasonsText ProblemBackwardsPrimaFacieReasonText

instance CoercibleForwards ProblemBackwardsConclusiveReasonsText ProblemBackwardsConclusiveReasonText

fromReasonBlocks :: forall input output. (CoercibleForwards input output) => input -> [(ProblemReasonName, output, ProblemVariablesText, ProblemStrengthDegree)]
fromReasonBlocks = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
    where
        p :: Parser (ProblemReasonName, output, ProblemVariablesText, ProblemStrengthDegree)
        p = do
            n <- parserProblemReasonName
            many space
            (t, (v, d)) <- many anyChar `precededBy` p'
            return (n, coerce  . (pack :: String -> Text) $ t, v, d)
            where
                p' :: Parser (ProblemVariablesText, ProblemStrengthDegree)
                p' = do
                    t <- parserProblemVariablesText
                    d <- parserProblemStrengthDegree
                    return (t, d)

--

--class Mereology whole parts where

--newtype ProblemVariableText = ProblemVariableText Text

--instance Mereology ProblemVariablesText [ProblemVariableText]

--type family MereologyPart whole :: *
--type instance MereologyPart ProblemVariablesText = [ProblemVariableText]

--type family MereologyWhole part :: *
--type instance MereologyWhole [ProblemVariableText] = ProblemVariablesText


--class (Coercible t Text) => IsBackwardsReasonText t where

--instance IsBackwardsReasonText ProblemBackwardsPrimaFacieReasonText

--instance IsBackwardsReasonText ProblemBackwardsConclusiveReasonText

--newtype IsBackwardsReasonText t => BackwardsPremisesText t = BackwardsPremisesText Text

--newtype BackwardsPremisesText t = BackwardsPremisesText Text

--newtype ConclusionText t = ConclusionText Text

--fromBackwardsReasonText :: forall t. IsBackwardsReasonText t => t -> (ForwardsPremisesText t, BackwardsPremisesText t, ConclusionText t)
--fromBackwardsReasonText = coerce . either (error . ppShow) id . runParser (p <* eof) () "" . coerce
--    where
--        p :: Parser (ForwardsPremisesText t, BackwardsPremisesText t, ConclusionText t)
--        p = pure (,,) <*> ft1 <*> ft2 <*> ft3
--            where
--                ft1 = map (ForwardsPremisesText  . pack) $ char '{' *> manyTill anyChar (char '}')
--                ft2 = map (BackwardsPremisesText . pack) $ many space *> char '{' *> manyTill anyChar (char '}')
--                ft3 = map (ConclusionText        . pack) $ many space *> string "||=>" *> many space *> many anyChar

--class (Coercible t Text) => IsForwardsReasonText t where

--newtype IsForwardsReasonText t => ForwardsPremisesText t = ForwardsPremisesText Text

--instance IsForwardsReasonText ProblemForwardsPrimaFacieReasonText

--instance IsForwardsReasonText ProblemForwardsConclusiveReasonText

--fromForwardsReasonText :: IsForwardsReasonText t => t -> (ForwardsPremisesText t, ConclusionText t)
--fromForwardsReasonText = coerce . either (error . ppShow) id . runParser (p <* eof) () ""
--    where
--        p :: Parser (ForwardsPremisesText t, ConclusionText Text)
--        p = pure (,) <*> ft1 <*> ft2
--            where
--                ft1 = map (ForwardsPremisesText . pack) $ char '{' *> manyTill anyChar (char '}')
--                ft2 = map (ConclusionText       . pack) $ many space *> string "||=>" *> many space *> many anyChar

--class (Coercible t Text, Coercible Text u) => IsCommaDelimitedText t u where

--instance IsCommaDelimitedText ProblemVariablesText ProblemVariableText

--instance IsCommaDelimitedText ProblemVariablesText ProblemVariableText



--fromCommaDelimitedText :: (MereologyWhole part ~ whole, MereologyPart whole ~ part) => whole -> part
--fromCommaDelimitedText = either (error . ppShow) id . runParser (many p <* eof) () ""
--    where
--        p :: Parser Text
--        p = map pack $ manyTill anyChar (many space *> (eof <|> (char ',' *> many space *> pure ())))

--data Formula 
--    =   FormulaQuantifier QuantifierType QuantifierVariable Formula
--    |   FormulaUnaryOperator UnaryOperatorType Formula
--    |   FormulaBinaryOperator BinaryOperatorType Formula Formula
--    |   FormulaTODO [Text]

--newtype Reason
--    deriving (Show)

--instance CoercibleForwards ProblemForwardsConclusiveReasonText ([Formula], Formula)

--
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

--
messageFromShow :: Show a => a -> IO ()
messageFromShow = putStrLn . pack . ppShow

messageFromShows :: Show a => [a] -> IO ()
messageFromShows = sequence_ . map messageFromShow

main :: IO ()
main = do
    combinedProblems <- ioProblemsTextFromFilePath $ fpFromString "combined-problems"
    --messageFromShow combinedProblems

    let problemTexts = problemTextsFromProblemsText combinedProblems
    --messageFromShows problemTexts

    let problemNumberAndAfterProblemNumberTexts = problemNumberAndAfterProblemNumberTextFromProblemText <$> problemTexts
    let problemNumbers = fst <$> problemNumberAndAfterProblemNumberTexts
    let afterProblemNumberTexts = snd <$> problemNumberAndAfterProblemNumberTexts
    --messageFromShows problemNumbers
    --messageFromShows afterProblemNumberTexts

    let problemDescriptionAndAfterProblemDescriptionTexts = problemDescriptionAndAfterProblemDescriptionTextFromAfterProblemNumberText <$> afterProblemNumberTexts
    let problemDescriptions = fst <$> problemDescriptionAndAfterProblemDescriptionTexts
    let afterProblemDescriptionTexts = snd <$> problemDescriptionAndAfterProblemDescriptionTexts
    --messageFromShows problemDescriptions
    --messageFromShows afterProblemDescriptionTexts
    
    let problemGivenPremisesTexts = sectionTextFromAfterProblemDescriptionText givenPremises <$> afterProblemDescriptionTexts
    --messageFromShows problemGivenPremisesTexts

    let problemUltimateEpistemicInterestsTexts = sectionTextFromAfterProblemDescriptionText ultimateEpistemicInterests <$> afterProblemDescriptionTexts
    --messageFromShows problemUltimateEpistemicInterestsTexts

    let problemForwardsPrimaFacieReasonsTexts = sectionTextFromAfterProblemDescriptionText forwardsPrimaFacieReasons <$> afterProblemDescriptionTexts
    --messageFromShows problemForwardsPrimaFacieReasonsTexts

    let problemForwardsConclusiveReasonsTexts = sectionTextFromAfterProblemDescriptionText forwardsConclusiveReasons <$> afterProblemDescriptionTexts
    --messageFromShows problemForwardsConclusiveReasonsTexts
    
    let problemBackwardsPrimaFacieReasonsTexts = sectionTextFromAfterProblemDescriptionText backwardsPrimaFacieReasons <$> afterProblemDescriptionTexts
    --messageFromShows problemBackwardsPrimaFacieReasonsTexts

    let problemBackwardsConclusiveReasonsTexts = sectionTextFromAfterProblemDescriptionText backwardsConclusiveReasons <$> afterProblemDescriptionTexts
    --messageFromShows problemBackwardsConclusiveReasonsTexts

    let problemGivenPremiseTextAndProblemJustificationDegrees = problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText <$> problemGivenPremisesTexts
    --messageFromShows problemGivenPremiseTextAndProblemJustificationDegrees

    let problemUltimateEpistemicInterestTextAndProblemJustificationDegrees = problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText <$> problemUltimateEpistemicInterestsTexts
    --messageFromShows problemUltimateEpistemicInterestTextAndProblemJustificationDegrees

    let reasonBlocksFromForwardsPrimaFacieReasonsTexts = fromReasonBlocks <$> problemForwardsPrimaFacieReasonsTexts
    messageFromShows reasonBlocksFromForwardsPrimaFacieReasonsTexts

    let reasonBlocksFromForwardsConclusiveReasonsTexts = fromReasonBlocks <$> problemForwardsConclusiveReasonsTexts
    --messageFromShows reasonBlocksFromForwardsConclusiveReasonsTexts

    let reasonBlocksFromBackwardsPrimaFacieReasonsTexts = fromReasonBlocks <$> problemBackwardsPrimaFacieReasonsTexts
    --messageFromShows reasonBlocksFromBackwardsPrimaFacieReasonsTexts

    let reasonBlocksFromBackwardsConclusiveReasonsTexts = fromReasonBlocks <$> problemBackwardsConclusiveReasonsTexts
    --messageFromShows reasonBlocksFromBackwardsConclusiveReasonsTexts

    return ()
