{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction #-}
module Oscar.Problem where

import Text.Parsec
import Text.Parsec.Expr
import Data.Char
import Data.String
import Data.Ratio
import Numeric
import Control.Applicative (pure, (<*>), (<*), (*>), (<$>), some)
--import Data.Functor

newtype
    ProblemNumber
  = ProblemNumber
    Int
  deriving Show

newtype
    ProblemDescription
  = ProblemDescription
    String
  deriving Show

type Key = String
type Amount = Rational  

data 
    Premise
  = Premise
      Key
      Amount
  deriving Show

data 
    UltimateEpistemicInterest
  = UltimateEpistemicInterest
      Key
      Amount
  deriving Show

data 
    ForwardsPrimaFacieReason
  = ForwardsPrimaFacieReason
      Key
      String
      Amount
  deriving Show

data
    Problem
  = Problem
      ProblemNumber
      ProblemDescription
      [Premise]
      --[UltimateEpistemicInterest]
      --[ForwardsPrimaFacieReason]
  deriving Show

  
----problem #(\d+)
----(.*?)
---- *given premises: *
----(^ *(.*?) *justification = (.*)$)+
---- *ultimate epistemic interests: *
----( *(.*?) *interest = (.*)$)+
---- *forwards prima facie reasons *
----(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
---- *backwards prima facie reasons *
----(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+
---- *forwards conclusive reasons *
----(^ *(.*?:) *\{(.*?)\} *\|\|=> *(.*?) *(variables = \{(.*?)\})? *strength = (.*?) *$)+
---- *backwards conclusive reasons *
----(^ *(.*?:) *\{(.*?)\} *\{(.*?)\} *\|\|=> *(.*?) *(variables = {(.*?)})? *strength = (.*?) *$)+

problemParser = Problem <$> 
  problemNumberParser 
    <*> 
  problemDescriptionParser 
    <*>
  (
    between 
      (string "")
      (optional $ (lookAhead $ string "Ultimate epistemic interests:"))
      problemPremisesParser
  )
  --  <*>
  --[UltimateEpistemicInterest "dummy" 1]
  --  <*>
  --[ForwardsPrimaFacieReason "dummy" 1]


problemNumberParser = ProblemNumber . read <$> 
  (string "Problem #" `between` newline $ many1 digit) <?> "number"

problemDescriptionParser = ProblemDescription <$> 
  manyTill anyChar (lookAhead (try (string  "\nGiven premises:" <?> "gp3") <|> (string "Given premises:" <?> "gp") <|> (eof >> string ""))) <?> "description"

problemPremisesParser = option [] $ try 
    (do
      ((( (try (string "\n") <?> "nl")) <|> (string "Given premises:" <?> "gp2")) <?> "asdf")
      sepBy (try problemPremiseParser) spaces <?> "premises")

problemPremiseParser = (\k j -> Premise k (fst . head $ readFloat j)) <$> 
  between spaces spaces (many1 alphaNum)
    <*> 
  between (string "justification = ") newline (many1 $ oneOf $ ['0'..'9'] ++ ".")
    <?> "premise"

main = do
  --putStrLn . show $ Problem (ProblemNumber 1) (ProblemDescription "hello world") [Premise "p1" 1]
  --putStrLn . show $ Problem (ProblemNumber 2) (ProblemDescription "goodbye world") [Premise "p1" 1, Premise "p2" (1 % 2)]
  parseTest problemParser test1
  parseTest problemParser test2
  parseTest problemParser test3
  parseTest problemParser test4
  parseTest problemParser test5
  main'
  --let test6 = test5 
  --    pp = problemParser 
  --  in do
  --    parseTest pp test6
  --    parseTest pp test6
  --let operatorTable = 
  --      [ 
  --        [Prefix ( ((\x -> ProblemNumber) . read) <$> string "Problem #")] 
  --      ]
  --    term = anyChar
  --    expr = buildExpressionParser operatorTable term
  --  in do
  --    parseTest expr testProblemNumber

testProblemNumber n = "Problem #" ++ show n ++ "\n"
testProblemDescription = "This is a case of collective rebutting defeat\n"
testPremises = "Given premises:\n     Pr2    justification = 0.2\n     A    justification = 1.0\n"
testUltimateEpistemicInterests = "Ultimate epistemic interests:\n     R    interest = 1.0\n"
testForwardsPrimaFacieReasons = "  FORWARDS PRIMA FACIE REASONS\n      pf-reason_1:   {P} ||=> Q   strength = 1.0\n      pf-reason_2:   {Q} ||=> R   strength = 1.0\n      pf-reason_3:   {C} ||=> ~R   strength = 1.0\n      pf-reason_4:   {B} ||=> C   strength = 1.0\n      pf-reason_5:   {A} ||=> B   strength = 1.0\n"
test1 = testProblemNumber 1 ++ testProblemDescription ++ testPremises ++ testUltimateEpistemicInterests ++ testForwardsPrimaFacieReasons
test2 = testProblemNumber 2                           ++ testPremises ++ testUltimateEpistemicInterests ++ testForwardsPrimaFacieReasons
test3 = testProblemNumber 3 ++ testProblemDescription ++ testPremises ++ testUltimateEpistemicInterests
test4 = testProblemNumber 4                           ++ testPremises ++ testUltimateEpistemicInterests
test5 = testProblemNumber 5                                           ++ testUltimateEpistemicInterests
tests = test1 ++ test2 ++ test3 ++ test4 ++ test5


data Section = 
    SectionBegin
  | SectionProblemNumber 
  | SectionProblemDescription
  | SectionPremises 
  | SectionUltimateEpistemicInterests 
  | SectionForwardsPrimaFacieReasons
  | SectionBackwardsPrimaFacieReasons
  | SectionForwardsConclusiveReasons
  | SectionBackwardsConclusiveReasons
  | SectionEnd
  deriving Show

data ProblemSection =
    PSNumber ProblemNumber
  | PSDescription ProblemDescription
  | PSPremise Premise
  | PSUltimateEpistemicInterest UltimateEpistemicInterest
  deriving Show


data TopLevelShit = TopLevelShit String

{-
  first, divide-up the text by ...
    Begin or newline followed by string "Problem #"
      then for each of these divide-up by 
        Begin or newline followed by "Problem #"
          consume: many1 digit ---> number
          newline
          many anyChar ---> description
          newline

          ...that followed by 
        Begin or newline followed by "Given premises:" >> spaces >> newline
        REQUIRED: Begin or newline followed by "Ultimate epistemic interests:" >> spaces >> newline
        newline followed by spaces >> "FORWARDS PRIMA FACIE REASONS" >> spaces >> newline

        newline followed by spaces >> "BACKWARDS PRIMA FACIE REASONS" >> spaces >> newline
        newline followed by spaces >> "FORWARDS CONCLUSIVE REASONS" >> spaces >> newline
        newline followed by spaces >> "BACKWARDS CONCLUSIVE REASONS" >> spaces >> newline
  
  
  
  
  
  [[start state] -> lookAhead parsec -> consumption parsec -> end state] -> problem builder  
-}

--lookBehind =
  

pp = do
  string "Problem #"
  n <- many1 digit
  newline
  --p <- manyTill anyChar $ ((lookAhead . try $ newline >> string "Problem #") >> newline >> return []) <|> (lookAhead $ eof >> return [])
  p <- manyTill anyChar $ (lookAhead  (lookAhead . try $ newline >> string "Problem #") >> newline >> return []) <|> (lookAhead $ eof >> return [])

  return (n, p)

myParserTest p u input = 
  case runParser p u "" input of
      Left err -> do putStr "parse error at "
                     print err
      Right x  -> print x

main' = do
  myParserTest (many pp) SectionBegin tests
