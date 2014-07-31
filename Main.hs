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

import ClassyPrelude hiding (Text, try)
import Control.Applicative
import Control.Conditional hiding (unlessM)
import Control.Monad
import Data.Char
import Data.Maybe (fromJust)
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
import Control.Monad.Free

import Formula
--import FormulaLexer (lexemesFromText)

--
simpleParse :: Parser a -> Text -> a
simpleParse p = either (error . ppShow) id . runParser p () ""

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

problemUltimateEpistemicInterestTextAndProblemInterestDegreesFromProblemUltimateEpistemicInterestsText :: ProblemSectionText UltimateEpistemicInterests -> [(ProblemUltimateEpistemicInterestText, ProblemInterestDegree)]
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
    char '{'
    (inner, _) <- (pack <$> many anyChar) `precededBy` char '}'
    let texts = simpleParse p inner
    return texts
    where
        p :: Parser [Text]
        p = do
            (firstText, restText) <- (many space *> (pack <$> many anyChar) <* many space) `precededBy` (lookAhead $ (eof *> pure False) <|> (char ',' *> many anyChar *> pure True))
            if restText then do
                char ','                
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
            many space
            (t, (v, d)) <- many anyChar `precededBy` p'
            --return (n, coerce  . (pack :: String -> Text) $ t, v, d)
            return $ ReasonBlock n (coerce  . (pack :: String -> Text) $ t) v d
            where
                p' :: Parser (ProblemVariablesText, ProblemStrengthDegree)
                p' = do
                    t <- parserProblemVariablesText
                    d <- parserProblemStrengthDegree
                    return (t, d)

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

messageFromShows10 :: Show a => String -> [a] -> IO ()
messageFromShows10 s xs = do
    print s
    messageFromShows $ take 10 xs

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

    --let testFormula1 :: Text = pack "(some x)((~AB) v C)"
    --goforit testFormula1

    let testFormula2 :: Text = pack "[(all x)[((F a) & ((F x) -> (F (g x)))) -> (F (g (g x)))] ->\n          (all x)[[(~(F a) v (F x)) v (F (g (g x)))] &\n               [(~(F a) v ~(F (g x))) v (F (g (g x)))]]]"
    goforit testFormula2
    --let testFormula :: Text = pack "x"


    --let ls = lexemesFromText $ pack "(some x)((~AB) v C)X"

    --print ls
    --putStrLn . pack . ppShow $ freeLexemes ls

    --print . runParser formulaParser () "" . lexemesFromText $ pack "(~AB v C)"

    return ()

goforit :: Text -> IO ()
goforit testFormula = do
    let tf1 :: [Char] = otoList testFormula
    let tf2 :: [Either Char Parenthesis] = (`eitherOr` tokenize) <$> tf1
    let tf3 :: [Either Parenthesis Char] = either Right Left <$> tf2
    let tf4 :: [Either Parenthesis [Char]] = mconcatRightPoints tf3
    let tf5 :: Free [] [Char] = treeFromParentheses id tf4
    let tf6 :: Free [] Text = map pack tf5
    putStrLn . pack . ppShow $ tf6
    let tf7 :: Free [] [LexemeWord] = map (simpleParse (many lexemeWord)) tf6
    putStrLn . pack . ppShow $ tf7
    let tf8 :: Free [] [Maybe LexemeQUOBOS] = map (map tokenize) tf7
    putStrLn . pack . ppShow $ tf8
    let tf9 :: Free [] [LexemeQUOBOS] = map (map fromJust) tf8
    putStrLn . pack . ppShow $ tf9
    let tf10 :: Free [] LexemeQUOBOS = joinFree tf9
    putStrLn . pack $ "tf10"
    putStrLn . pack . ppShow $ tf10
    let tf11 :: Free [] LexemeQUOBOS = simplify tf10
    putStrLn . pack $ "tf11"
    putStrLn . pack . ppShow $ tf11
    let tf12 :: Free [] PrefixBinary = prefix tf11
    putStrLn . pack $ "tf12"
    putStrLn . pack . ppShow $ tf12
    let tf13 :: Free [] PrefixBinary = simplify tf12
    putStrLn . pack $ "tf13"
    putStrLn . pack . ppShow $ tf13
    let tf14 :: Free [] PrefixBinaryUnary = prefix2 tf13
    putStrLn . pack $ "tf14"
    putStrLn . pack . ppShow $ tf14

joinFree :: Functor f => Free f (f a) -> Free f a
joinFree (Pure as) = Free (map Pure as)
joinFree (Free fs) = Free $ map joinFree fs
