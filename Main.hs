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
{-# LANGUAGE UndecidableInstances #-}

module Main where

import ClassyPrelude hiding (
    --Text, 
    try, 
    undefined,
    )
import Prelude (undefined)

import Control.Applicative
import Control.Conditional hiding (unlessM)
import Control.Monad
--import Control.Monad.Free
--import Data.Char
import Data.Coerce
--import Data.Maybe (fromJust)
--import Data.Set (Set)
--import Data.Tagged
--import Data.Text.Internal.Lazy (Text)
--import Numeric (readFloat, readSigned)
import Prelude (read)
--import Safe
import Text.Parsec hiding ((<|>), many)
--import Text.Parsec.Text.Lazy
import Text.Parsec.Text
import Text.Show.Pretty (ppShow)

--import qualified Data.Set as Set

import Formula
import Utilities
--import FormulaLexer (lexemesFromText)

--
newtype ProblemsText = ProblemsText Text
    deriving (Show)

ioProblemsTextFromFilePath :: FilePath -> IO ProblemsText
ioProblemsTextFromFilePath = map ProblemsText . readFile

--
newtype ProblemText = ProblemText Text
    deriving (Show)

problemTextsFromProblemsText :: ProblemsText -> [ProblemText]
problemTextsFromProblemsText = map ProblemText . simpleParse (many p) . coerce
    where
        p :: Parser Text
        p = do
            spaces
            _ <- string "Problem #"
            pack <$> manyTill anyChar endP

        endP :: Parser ()
        endP = eof <|> (pure () <* (lookAhead . try $ string "Problem #"))

--
newtype AfterProblemNumberText = AfterProblemNumberText Text
    deriving (Show)

newtype ProblemNumber = ProblemNumber Int
    deriving (Show)

problemNumberAndAfterProblemNumberTextFromProblemText :: ProblemText -> (ProblemNumber, AfterProblemNumberText)
problemNumberAndAfterProblemNumberTextFromProblemText = simpleParse p . coerce
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
problemDescriptionAndAfterProblemDescriptionTextFromAfterProblemNumberText = simpleParse p . coerce
    where
        p :: Parser (ProblemDescription, AfterProblemDescriptionText)
        p = do
            _ <- many space
            n <- ProblemDescription . pack <$> manyTill anyChar (lookAhead . try $ many space >> sectionParser)
            t <- pack <$> many anyChar
            return (n, AfterProblemDescriptionText t)

--
class IsAKind k where

instance IsAKind GivenPremises
instance IsAKind UltimateEpistemicInterests
instance IsAKind (Reasons direction defeasible)

newtype IsAKind kind => ProblemSectionText kind = ProblemSectionText Text
    deriving (Show)

class HasSection s where
    section :: s -> Section

data GivenPremises              = GivenPremises
data UltimateEpistemicInterests = UltimateEpistemicInterests

data Direction = Forwards | Backwards
    deriving (Show)

data Defeasibility = PrimaFacie | Conclusive
    deriving (Show)

data Reasons (direction :: Direction) (defeasible :: Defeasibility) = Reasons

instance HasSection GivenPremises                  where section _ = Section'GivenPremises
instance HasSection UltimateEpistemicInterests     where section _ = Section'UltimateEpistemicInterests
instance HasSection (Reasons Forwards  PrimaFacie) where section _ = Section'ForwardsPrimaFacieReasons
instance HasSection (Reasons Forwards  Conclusive) where section _ = Section'ForwardsConclusiveReasons
instance HasSection (Reasons Backwards PrimaFacie) where section _ = Section'BackwardsPrimaFacieReasons
instance HasSection (Reasons Backwards Conclusive) where section _ = Section'BackwardsConclusiveReasons

problemSectionTextFromAfterProblemDescriptionText :: forall kind. (HasSection kind) => AfterProblemDescriptionText -> ProblemSectionText kind
problemSectionTextFromAfterProblemDescriptionText = coerce . rawSection (section kind) . coerce
  where
    kind :: kind = undefined

    rawSection :: Section -> Text -> Text
    rawSection _section = simpleParse $ do
        _ <- manyTill anyChar $ lookAhead . try $ eof <|> guardM (map (== _section) sectionParser)
        p' <|> pure (pack "")
      where
        p' :: Parser Text
        p' = do
            guardM (map (== _section) sectionParser)
            pack <$> manyTill anyChar (lookAhead . try $ eof <|> (space >> sectionParser >> pure ()))

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

problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText :: ProblemSectionText GivenPremises -> [(ProblemGivenPremiseText, ProblemJustificationDegree)]
problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
    where
        p :: Parser (ProblemGivenPremiseText, ProblemJustificationDegree)
        p = do
            spaces
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

problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText :: ProblemSectionText UltimateEpistemicInterests -> [(ProblemUltimateEpistemicInterestText, ProblemInterestDegree)]
problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
    where
        p :: Parser (ProblemUltimateEpistemicInterestText, ProblemInterestDegree)
        p = do
            spaces
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
newtype ProblemReasonText (direction :: Direction) (defeasible :: Defeasibility) = ProblemReasonText Text
    deriving (Show)

data ReasonBlock (direction :: Direction) (defeasible :: Defeasibility) = ReasonBlock
    {   _rbProblemReasonName     :: ProblemReasonName
    ,   _rbProblemReasonText     :: (ProblemReasonText (direction :: Direction) (defeasible :: Defeasibility))
    ,   _rbProblemVariablesText  :: ProblemVariablesText
    ,   _rbProblemStrengthDegree :: ProblemStrengthDegree
    }   deriving (Show)

extractFromProblemReasonTextForwards :: ProblemReasonText Forwards defeasible -> ([Text], Text)
extractFromProblemReasonTextForwards = simpleParse p . coerce
    where
        p :: Parser ([Text], Text)
        p = do
            (premiseTexts, _) <- enbracedListParser `precededBy` (many space >> string "||=>" >> many space)
            conclusionText <- pack <$> many anyChar
            return (premiseTexts, conclusionText)

enbracedListParser :: Parser [Text]
enbracedListParser = do
    _ <- char '{'
    (inner, _) <- (pack <$> many anyChar) `precededBy` char '}'
    let texts = simpleParse p inner
    return texts
    where
        p :: Parser [Text]
        p = do
            (firstText, restText) <- (many space *> (pack <$> many anyChar) <* many space) `precededBy` (lookAhead $ (eof *> pure False) <|> (char ',' *> many anyChar *> pure True))
            if restText then do
                _ <- char ','
                restTexts <- p
                return $ firstText : restTexts
            else do
                return [firstText]

reasonBlocksFromProblemSectionText :: forall direction defeasible.
    (ProblemSectionText (Reasons (direction :: Direction) (defeasible :: Defeasibility))) ->
    [ReasonBlock (direction :: Direction) (defeasible :: Defeasibility)]
    --  [(ProblemReasonName, ProblemReasonText (direction :: Direction) (defeasible :: Defeasibility), ProblemVariablesText, ProblemStrengthDegree)]
reasonBlocksFromProblemSectionText = simpleParse (many (try p) <* many space <* eof) . coerce
    where
        --p :: Parser (ProblemReasonName, ProblemReasonText (direction :: Direction) (defeasible :: Defeasibility), ProblemVariablesText, ProblemStrengthDegree)
        p :: Parser (ReasonBlock (direction :: Direction) (defeasible :: Defeasibility))
        p = do
            n <- parserProblemReasonName
            spaces
            (t, (v, d)) <- many anyChar `precededBy` p'
            --return (n, coerce  . (pack :: String -> Text) $ t, v, d)
            return $ ReasonBlock n (coerce  . (pack :: String -> Text) $ t) v d
            where
                p' :: Parser (ProblemVariablesText, ProblemStrengthDegree)
                p' = do
                    t <- parserProblemVariablesText
                    d <- parserProblemStrengthDegree
                    return (t, d)

main :: IO ()
main = do
    combinedProblems <- ioProblemsTextFromFilePath $ fpFromString "combined-problems"
    messageFromShow combinedProblems

    let problemTexts = problemTextsFromProblemsText combinedProblems
    messageFromShows problemTexts

    let problemNumberAndAfterProblemNumberTexts = problemNumberAndAfterProblemNumberTextFromProblemText <$> problemTexts
    let problemNumbers = fst <$> problemNumberAndAfterProblemNumberTexts
    let afterProblemNumberTexts = snd <$> problemNumberAndAfterProblemNumberTexts
    messageFromShows problemNumbers
    messageFromShows afterProblemNumberTexts

    let problemDescriptionAndAfterProblemDescriptionTexts = problemDescriptionAndAfterProblemDescriptionTextFromAfterProblemNumberText <$> afterProblemNumberTexts
    let problemDescriptions = fst <$> problemDescriptionAndAfterProblemDescriptionTexts
    let afterProblemDescriptionTexts = snd <$> problemDescriptionAndAfterProblemDescriptionTexts
    messageFromShows problemDescriptions
    messageFromShows afterProblemDescriptionTexts

    let problemGivenPremisesTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemGivenPremisesTexts

    let problemUltimateEpistemicInterestsTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemUltimateEpistemicInterestsTexts

    let problemForwardsPrimaFacieReasonsTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemForwardsPrimaFacieReasonsTexts

    let problemForwardsConclusiveReasonsTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemForwardsConclusiveReasonsTexts

    let problemBackwardsPrimaFacieReasonsTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemBackwardsPrimaFacieReasonsTexts

    let problemBackwardsConclusiveReasonsTexts = problemSectionTextFromAfterProblemDescriptionText <$> afterProblemDescriptionTexts
    messageFromShows problemBackwardsConclusiveReasonsTexts

    let problemGivenPremiseTextAndProblemJustificationDegrees = problemGivenPremiseTextAndProblemJustificationDegreesFromProblemGivenPremisesText <$> problemGivenPremisesTexts
    messageFromShows problemGivenPremiseTextAndProblemJustificationDegrees

    let problemUltimateEpistemicInterestTextAndProblemJustificationDegrees = problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText <$> problemUltimateEpistemicInterestsTexts
    messageFromShows problemUltimateEpistemicInterestTextAndProblemJustificationDegrees

    let reasonBlocksFromForwardsPrimaFacieReasonsTexts :: [[ReasonBlock Forwards PrimaFacie]] = reasonBlocksFromProblemSectionText <$> problemForwardsPrimaFacieReasonsTexts
    messageFromShows reasonBlocksFromForwardsPrimaFacieReasonsTexts

    let reasonBlocksFromForwardsConclusiveReasonsTexts :: [[ReasonBlock Forwards Conclusive]] = reasonBlocksFromProblemSectionText <$> problemForwardsConclusiveReasonsTexts
    messageFromShows reasonBlocksFromForwardsConclusiveReasonsTexts

    let reasonBlocksFromBackwardsPrimaFacieReasonsTexts :: [[ReasonBlock Backwards PrimaFacie]] = reasonBlocksFromProblemSectionText <$> problemBackwardsPrimaFacieReasonsTexts
    messageFromShows reasonBlocksFromBackwardsPrimaFacieReasonsTexts

    let reasonBlocksFromBackwardsConclusiveReasonsTexts :: [[ReasonBlock Backwards Conclusive]] = reasonBlocksFromProblemSectionText <$> problemBackwardsConclusiveReasonsTexts
    messageFromShows reasonBlocksFromBackwardsConclusiveReasonsTexts

    --let reasonBlocksFromForwardsPrimaFacieReasonsTexts :: [[(ProblemReasonName, ProblemReasonText Forwards PrimaFacie, ProblemVariablesText, ProblemStrengthDegree)]] = fromReasonBlocks <$> problemForwardsPrimaFacieReasonsTexts
    --messageFromShows reasonBlocksFromForwardsPrimaFacieReasonsTexts

    --let reasonBlocksFromForwardsConclusiveReasonsTexts :: [[(ProblemReasonName, ProblemReasonText Forwards Conclusive, ProblemVariablesText, ProblemStrengthDegree)]] = fromReasonBlocks <$> problemForwardsConclusiveReasonsTexts
    --messageFromShows reasonBlocksFromForwardsConclusiveReasonsTexts

    --let reasonBlocksFromBackwardsPrimaFacieReasonsTexts :: [[(ProblemReasonName, ProblemReasonText Backwards PrimaFacie, ProblemVariablesText, ProblemStrengthDegree)]] = fromReasonBlocks <$> problemBackwardsPrimaFacieReasonsTexts
    --messageFromShows reasonBlocksFromBackwardsPrimaFacieReasonsTexts

    --let reasonBlocksFromBackwardsConclusiveReasonsTexts :: [[(ProblemReasonName, ProblemReasonText Backwards Conclusive, ProblemVariablesText, ProblemStrengthDegree)]] = fromReasonBlocks <$> problemBackwardsConclusiveReasonsTexts
    --messageFromShows reasonBlocksFromBackwardsConclusiveReasonsTexts

    messageFromShows10 "***ForwardsPrimaFacieReasons***" $ map _rbProblemReasonText <$> reasonBlocksFromForwardsPrimaFacieReasonsTexts

    let forwardsPremisesTexts :: [[([Text], Text)]] = map extractFromProblemReasonTextForwards . map _rbProblemReasonText <$> reasonBlocksFromForwardsPrimaFacieReasonsTexts
    messageFromShows forwardsPremisesTexts
    messageFromShows10 "forwardsPremisesTexts" forwardsPremisesTexts

    let forwardsPremisesTexts' :: [[([Text], Text)]] = map extractFromProblemReasonTextForwards . map _rbProblemReasonText <$> reasonBlocksFromForwardsConclusiveReasonsTexts
    messageFromShows forwardsPremisesTexts'

    let testFormula2 :: Text = pack "[~~(all x)~~[((F a) & ((F x) -> (F (g x)))) -> (F (g (g x)))] ->\n          (all x)[[(~(F a) v (F x)) v (F (g (g x)))] &\n               [(~(F a) v ~~~(F (g x))) v (F (g ((g x))))]]]"

    let tf2 = formulaFromText testFormula2
    putStrLn . pack . ppShow $ tf2

    return ()
