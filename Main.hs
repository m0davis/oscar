{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

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
import Text.Parsec                      (lookAhead)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (option)
import Text.Parsec                      (runParser)
import Text.Parsec                      (space)
import Text.Parsec                      (spaces)
import Text.Parsec                      (string)
import Text.Parsec                      (try)
import Text.Parsec.Text                 (Parser)
import Text.Show.Pretty                 (ppShow)

import Oscar.Formula                    (formulaFromText)
import Oscar.Utilities                  (messageFromShow)
import Oscar.Utilities                  (messageFromShows)
import Oscar.Utilities                  (messageFromShows10)
import Oscar.Utilities                  (precededBy)
import Oscar.Utilities                  (simpleParse)

--
newtype ProblemsText = ProblemsText Text
    deriving (Show)

problemsTextM :: FilePath -> IO ProblemsText
problemsTextM = map ProblemsText . readFile

--
newtype ProblemText = ProblemText Text
    deriving (Show)

problemTexts :: ProblemsText -> [ProblemText]
problemTexts = map ProblemText . simpleParse (many p) . coerce
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

splitAfterProblemNumber :: ProblemText -> (ProblemNumber, AfterProblemNumberText)
splitAfterProblemNumber = simpleParse p . coerce
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

splitAfterProblemNumberText :: AfterProblemNumberText -> (ProblemDescription, AfterProblemDescriptionText)
splitAfterProblemNumberText = simpleParse p . coerce
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

problemSectionText :: forall kind. (HasSection kind) => AfterProblemDescriptionText -> ProblemSectionText kind
problemSectionText = coerce . rawSection (section kind) . coerce
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

problemGivenPremiseTextAndProblemJustificationDegrees :: ProblemSectionText GivenPremises -> [(ProblemGivenPremiseText, ProblemJustificationDegree)]
problemGivenPremiseTextAndProblemJustificationDegrees = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
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

problemUltimateEpistemicInterestTextAndProblemInterestDegrees :: ProblemSectionText UltimateEpistemicInterests -> [(ProblemUltimateEpistemicInterestText, ProblemInterestDegree)]
problemUltimateEpistemicInterestTextAndProblemInterestDegrees = either (error . ppShow) id . runParser (many (try p) <* many space <* eof) () "" . coerce
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

reasonBlocks :: forall direction defeasible.
    (ProblemSectionText (Reasons (direction :: Direction) (defeasible :: Defeasibility))) ->
    [ReasonBlock (direction :: Direction) (defeasible :: Defeasibility)]
    --  [(ProblemReasonName, ProblemReasonText (direction :: Direction) (defeasible :: Defeasibility), ProblemVariablesText, ProblemStrengthDegree)]
reasonBlocks = simpleParse (many (try p) <* many space <* eof) . coerce
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
    combinedProblems <- problemsTextM $ fpFromString "combined-problems"
    messageFromShow combinedProblems

    let problemTexts' = problemTexts combinedProblems
    messageFromShows problemTexts'

    let problemNumberAndAfterProblemNumberTexts = splitAfterProblemNumber <$> problemTexts'
    let problemNumbers = fst <$> problemNumberAndAfterProblemNumberTexts
    let afterProblemNumberTexts = snd <$> problemNumberAndAfterProblemNumberTexts
    messageFromShows problemNumbers
    messageFromShows afterProblemNumberTexts

    let problemDescriptionAndAfterProblemDescriptionTexts = splitAfterProblemNumberText <$> afterProblemNumberTexts
    let problemDescriptions = fst <$> problemDescriptionAndAfterProblemDescriptionTexts
    let afterProblemDescriptionTexts = snd <$> problemDescriptionAndAfterProblemDescriptionTexts
    messageFromShows problemDescriptions
    messageFromShows afterProblemDescriptionTexts

    let problemGivenPremisesTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemGivenPremisesTexts

    let problemUltimateEpistemicInterestsTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemUltimateEpistemicInterestsTexts

    let problemForwardsPrimaFacieReasonsTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemForwardsPrimaFacieReasonsTexts

    let problemForwardsConclusiveReasonsTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemForwardsConclusiveReasonsTexts

    let problemBackwardsPrimaFacieReasonsTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemBackwardsPrimaFacieReasonsTexts

    let problemBackwardsConclusiveReasonsTexts = problemSectionText <$> afterProblemDescriptionTexts
    messageFromShows problemBackwardsConclusiveReasonsTexts

    let problemGivenPremiseTextAndProblemJustificationDegrees' = problemGivenPremiseTextAndProblemJustificationDegrees <$> problemGivenPremisesTexts
    messageFromShows problemGivenPremiseTextAndProblemJustificationDegrees'

    let problemUltimateEpistemicInterestTextAndProblemInterestDegrees' = problemUltimateEpistemicInterestTextAndProblemInterestDegrees <$> problemUltimateEpistemicInterestsTexts
    messageFromShows problemUltimateEpistemicInterestTextAndProblemInterestDegrees'

    let reasonBlocksFromForwardsPrimaFacieReasonsTexts :: [[ReasonBlock Forwards PrimaFacie]] = reasonBlocks <$> problemForwardsPrimaFacieReasonsTexts
    messageFromShows reasonBlocksFromForwardsPrimaFacieReasonsTexts

    let reasonBlocksFromForwardsConclusiveReasonsTexts :: [[ReasonBlock Forwards Conclusive]] = reasonBlocks <$> problemForwardsConclusiveReasonsTexts
    messageFromShows reasonBlocksFromForwardsConclusiveReasonsTexts

    let reasonBlocksFromBackwardsPrimaFacieReasonsTexts :: [[ReasonBlock Backwards PrimaFacie]] = reasonBlocks <$> problemBackwardsPrimaFacieReasonsTexts
    messageFromShows reasonBlocksFromBackwardsPrimaFacieReasonsTexts

    let reasonBlocksFromBackwardsConclusiveReasonsTexts :: [[ReasonBlock Backwards Conclusive]] = reasonBlocks <$> problemBackwardsConclusiveReasonsTexts
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
