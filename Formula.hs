{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Formula where

import ClassyPrelude hiding (Text, try)
import Text.Show.Pretty (ppShow)

import Numeric.Natural
import Data.Pointed
import Control.Applicative
import Control.Monad
import Control.Lens hiding (uncons)
import Control.Monad.Free
import Data.Either.Utils (maybeToEither)
import Data.Text.Internal.Lazy (Text)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim hiding ((<|>), many, uncons)
import Text.Parsec.String ()
import Text.Parsec.Text.Lazy

--
data Parenthesis = OpenParenthesis | CloseParenthesis
    deriving (Bounded, Eq, Read, Show)

class Tokenizer from to where
    tokenize :: from -> Maybe to

instance Tokenizer Char Parenthesis where
    tokenize '(' = Just OpenParenthesis
    tokenize '[' = Just OpenParenthesis
    tokenize ')' = Just CloseParenthesis
    tokenize ']' = Just CloseParenthesis
    tokenize _   = Nothing

mconcatRightPoints :: 
    (Pointed p, Semigroup s, p r ~ s) => 
    [Either l r] -> 
    [Either l s]
mconcatRightPoints [] = []
mconcatRightPoints (Left l : xs) = Left l : mconcatRightPoints xs
mconcatRightPoints (Right r : xs) = case mconcatRightPoints xs of
    (Right rs : ys) -> Right (point r <> rs) : ys
    ys              -> Right (point r      ) : ys

eitherOr :: 
    a -> 
    (a -> Maybe b) -> 
    Either a b
eitherOr a f = maybeToEither a (f a)

treeFromParentheses ::
    forall as a b.
    (IsSequence as, Element as ~ a) =>
    (a -> Either Parenthesis b) ->
    as ->
    Free [] b
treeFromParentheses f = fst . tfp 0 []
    where

    tfp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    tfp d prev ass
        |   onull ass =
                (Free prev, mempty)
        |   otherwise =
                case f a of
                    Left OpenParenthesis ->
                        let (paren, rest) = tfp (succ d) [] as
                        in  tfp d (prev ++ [paren]) rest
                    Left CloseParenthesis ->
                        case d of
                            0 -> error "unexpected CloseParenthesis at depth 0"
                            _ -> (Free prev, as)
                    Right b -> -- ^?! _Right
                        tfp d (prev ++ [Pure b]) as
        where
            Just (a, as) = uncons ass


newtype LexemeWord = LexemeWord Text
    deriving (Show)

lexemeWord :: Parser LexemeWord
lexemeWord = {-(LexemeWord . pack) <$> -}do
    many space
    (
        empty
        <|> (char '~' >>= (return . LexemeWord . pack . point))
        <|> (manyTill anyChar (eof <|> (lookAhead $ (space *> pure ()) <|> (char '~' *> pure ()))) >>= (return . LexemeWord . pack))
        )



{-
-- | formula text (sans parentheses) -> list of symbols
data Quantifier
    =   Quantifier_Universal
    |   Quantifier_Existential

data UnaryOperator
    =   UnaryOperator_Negation
    |   UnaryOperator_Whether

data BinaryOperator
    =   BinaryOperator_Conjunction
    |   BinaryOperator_Disjunction
    |   BinaryOperator_Conditional
    |   BinaryOperator_Biconditional
    |   BinaryOperator_Defeater

data LexemeQUOBOS a
    =   LexemeQUOBOS_Quantifier Quantifier
    |   LexemeQUOBOS_UnaryOperator UnaryOperator
    |   LexemeQUOBOS_BinaryOperator BinaryOperator
    |   LexemeQUOBOS_Symbol a

:: ParsecT Text u m (LexemeQUOBOS Text)
= 

ParsecT Text u m Lexer1Char






freeLexemes :: [Lexeme] -> Free [] Lexeme
freeLexemes ls = Free . fst $ foo ls
    where

    foo :: [Lexeme] -> ([Free [] Lexeme], [Lexeme])
    foo xss
        | endsOnLastSymbol xss = ([], [])
        | endsOnClosingParenthesis xss = ([], xs)
        | openParen x = 
                let (fs, rest) = foo xs in
                    let (rs, rest') = foo rest in
                        (Free fs : rs, rest')
        | otherwise = let (fs, rest) = foo xs in (Pure x : fs, rest)
        where
            (x:xs) = xss

whetherOpenParenthesis :: (IsSequence es, Element es ~ e) => Either es Parenthesis -> Either es True

Text -> Free [] Text -- derivable, with some help?

Text -> [LexemeWord Text]

newtype LexemeWord a = LexemeWord a

whetherQuantifier :: Text -> Maybe Quantifier  -- Char module?

Text -> [LexemeQUOBOS]

Free [] Text -> Free [] LexemeQUOBOS

{-
"A ((B C) D)"                                                                :: L0Text
     [Pure "A"     , Free [Free [Pure "B C"           ], Pure "D"     ]]     :: [Free [] L1Text]
Free [Pure "A"     , Free [Free [Pure "B C"           ], Pure "D"     ]]     :: Free [] L1Text
Free [Pure [A]     , Free [Free [Pure [B, C]          ], Pure [D]     ]]     :: Free [] [LexemeQUOBOS]
Free [Free [Pure A], Free [Free [Free [Pure B, Pure C]], Free [Pure D]]]     :: Free [] LexemeQUOBOS
-}
--

-- | tree of lists of symbols -> expression
data Expression
    =   Expression_Quantification Quantifier Symbol Expression
    |   Expression_UnaryOperation UnaryOperator Expression
    |   Expression_BinaryOperation BinaryOperator Expression Expression
    |   Expression_Predication Symbol [Free [] Symbol]

Free [] LexemeQOS -> Expression

Free [] LexemeQOS -> Maybe Expression -- Quantification, UnaryOperation, BinaryOperation, Predication, [Free [] Symbol]























--
runLexer_Parentheses :: L0Text -> [Lexer1]


pLexer1OpenParenthesis :: ParsecT Text u m Lexer1Char
pLexer1OpenParenthesis = oneOf "([" *> pure Lexer1Char_OpenParenthesis

pLexer1CloseParenthesis :: ParsecT Text u m Lexer1Char
pLexer1CloseParenthesis = oneOf ")]" *> pure Lexer1Char_CloseParenthesis

pLexer1CharChar :: ParsecT Text u m Lexer1Char
pLexer1CharChar = notFollowedBy pLexer1OpenParenthesis >> pLexer1CloseParenthesis >> Lexer1Char_Char <$> anyChar *> pure Lexer1Char_CloseParenthesis

pLexer1Char :: ParsecT Text u m Lexer1Char
pLexer1Char = empty
    <|> (char '(' *> Lexer1Char_OpenParenthesis)
    <|> (char '[' *> Lexer1Char_OpenParenthesis)
    <|> (char ')' *> Lexer1Char_CloseParenthesis)
    <|> (char ']' *> Lexer1Char_CloseParenthesis)
    <|> (Lexer1Char_Char <$> anyChar)

-- | L0Text = formula text
-- | L1Text = formula text sans parentheses
data Lexer1
    =   Lexer1_OpenParenthesis
    |   Lexer1_CloseParenthesis
    |   Lexer1_Text1 L1Text

runLexer_Parentheses :: L0Text -> [Lexer1]
runLexer_Parentheses =
    rl :: ParsecT Text u m Lexer1
    rl = empty
        <|> (char '(' *> pure Lexer1_OpenParenthesis)
        <|> (char ')' *> pure Lexer1_CloseParenthesis)
        <|> (char ')' *> pure Lexer1_CloseParenthesis)
        where

        ch :: ParsecT Text u m Char
        ch = 

runFree_Parentheses :: [Lexer1] -> [Free [] L1Text]
--




--
data Lexeme
    =   Lexeme_OpenParentheses
    |   Lexeme_CloseParentheses
    |   Lexeme_Negation
    |   Lexeme_Whether
    |   Lexeme_Disjunction
    |   Lexeme_Conjunction
    |   Lexeme_Conditional
    |   Lexeme_Biconditional
    |   Lexeme_Defeats
    |   Lexeme_Symbol Text
    deriving (Eq, Show)

--

type TParser = Parsec Text ()

tpChar :: TParser Char
tpChar = notFollowedBy space >> notFollowedBy (oneOf "([])") >> anyChar

tpLexeme :: TParser Lexeme
tpLexeme = many space *>
    (
        empty
        <|> (char '('                     *> pure Lexeme_OpenParentheses )
        <|> (char '['                     *> pure Lexeme_OpenParentheses )
        <|> (char ')'                     *> pure Lexeme_CloseParentheses)
        <|> (char ']'                     *> pure Lexeme_CloseParentheses)
        <|> (char '~'                     *> pure Lexeme_Negation        )
        <|> (char '?'                     *> pure Lexeme_Whether         )
        <|> try (char 'v'      *> space   *> pure Lexeme_Disjunction     )
        <|> try (char '&'      *> space   *> pure Lexeme_Conjunction     )
        <|> try (string "->"   *> space   *> pure Lexeme_Conditional     )
        <|> try (string "<->"  *> space   *> pure Lexeme_Biconditional   )
        <|> try (char '@'      *> space   *> pure Lexeme_Defeats         )
        <|> try (many1 tpChar <**> pure (Lexeme_Symbol . pack))
        <|> (many space *> empty)
    )

lexemesFromText :: Text -> [Lexeme]
lexemesFromText = either (error . ppShow) id . runParser (many tpLexeme) () ""

--

endsOnClosingParenthesis :: [Lexeme] -> Bool
endsOnClosingParenthesis (Lexeme_CloseParentheses : _) = True
endsOnClosingParenthesis [] = error "missing a closing parenthesis"
endsOnClosingParenthesis _ = False

endsOnLastSymbol :: [Lexeme] -> Bool
endsOnLastSymbol [] = True
endsOnLastSymbol _ = False

openParen :: Lexeme -> Bool
openParen Lexeme_OpenParentheses = True
openParen _ = False

freeLexemes :: [Lexeme] -> Free [] Lexeme
freeLexemes ls = Free . fst $ foo ls
    where

    foo :: [Lexeme] -> ([Free [] Lexeme], [Lexeme])
    foo xss
        | endsOnLastSymbol xss = ([], [])
        | endsOnClosingParenthesis xss = ([], xs)
        | openParen x = 
                let (fs, rest) = foo xs in
                    let (rs, rest') = foo rest in
                        (Free fs : rs, rest')
        | otherwise = let (fs, rest) = foo xs in (Pure x : fs, rest)
        where
            (x:xs) = xss

--

data Lex2
    =   Quantifier [Symbol]
    |   PrefixOperator Operator 
    |   InfixOperator Operator Lex2 Lex2

--lpFreeLexemes :: LParser (Free [] Lexeme)
--lpFreeLexemes = do
--    empty
--    <|> (lpLexeme Lexeme_OpenParentheses  *> (lpFreeLexemes >>= return . Free []))
--    <|> (manyTill () (lpLexeme Lexeme))
--    <|> (lpLexeme Lexeme_CloseParentheses *> (lpFreeLexemes >>= Free []))
--    where

--data Term
--    =   Term_Lexemes [Lexeme]
--    |   Term_Unary Lexeme Term
--    |   Term_Binary Lexeme Term Term

--type TermOperatorTable = OperatorTable [Lexeme] () Identity Term

--termOperatorTable :: TermOperatorTable
--termOperatorTable = 
--    [   [   
--        ]
--    ]

--

type LParser = Parsec [Lexeme] ()

lpLexeme :: Lexeme -> LParser Lexeme
lpLexeme lexe = token show (const $ initialPos "") $ \ l -> if l == lexe then Just l else Nothing

lpSymbol :: Text -> LParser Lexeme
lpSymbol = lpLexeme . Lexeme_Symbol

lpAnySymbol :: LParser Lexeme
lpAnySymbol = token show (const $ initialPos "") $ \case
    Lexeme_Symbol text -> Just (Lexeme_Symbol text)
    _ -> Nothing
   
--

data Expression
    =   OpenParentheses
    |   CloseParentheses
    |   Negation
    |   Whether
    |   Disjunction
    |   Conjunction
    |   Conditional
    |   Biconditional
    |   Defeats
    |   Symbol Text
    deriving (Eq, Show)

data Formula 
    =   Formula'UnaryOperator UnaryOperator Formula
    |   Formula'BinaryOperator Formula BinaryOperator Formula
    |   Formula'Predicate Predicate [DomainFunction]
    deriving (Show)

data UnaryOperator
    =   UnaryOperator'Not
    |   UnaryOperator'Quantifier QuantifierOperator Variable
    |   UnaryOperator'Whether
    deriving (Show)

data BinaryOperator
    =   BinaryOperator'Or
    |   BinaryOperator'And
    |   BinaryOperator'Defeats
    |   BinaryOperator'Conditional
    |   BinaryOperator'Biconditional
    deriving (Show)

newtype Predicate = Predicate Text
    deriving (Show)

data QuantifierOperator = Quantifier'All | Quantifier'Some
    deriving (Show)

data DomainFunction 
    =   DomainFunction'Function Variable [DomainFunction]
    |   DomainFunction'Simple Variable
    |   DomainFunction'Identity DomainFunction DomainFunction
    deriving (Show)

newtype Variable = Variable Text
    deriving (Show)

symbolAs :: (Text -> a) -> LParser a
symbolAs f = lpAnySymbol >>= ( \ (Lexeme_Symbol t) -> return (f t) )

variable :: LParser Variable
variable = symbolAs Variable

predicate :: LParser Predicate
predicate = symbolAs Predicate

-- 

(->>) :: LParser a -> b -> LParser b
p ->> v = p *> pure v

-- ~(all x)(F x) v G




--binaryParser :: LParser Formula
--binaryParser = 
--    empty
--    <|> (try (lookAhead (unaryParser *> operator *> unaryParser)) *> )
--    try negation <|> try quantifier <|> try binary <|> try parenthetic <|> try formulaPredicate

--unaryParser :: LParser Formula
--unaryParser = try unary <|> try binary <|> try parenthetic <|> try formulaPredicate

--unary :: LParser Formula
--unary = try quantifier <|> try negation <|> try whether

--quantifier :: LParser Formula
--quantifier = do
--    lpLexeme OpenParentheses
--    q <- quantifierOperator
--    v <- variable
--    lpLexeme CloseParentheses
--    lpLexeme OpenParentheses
--    f <- topLevelParser
--    lpLexeme CloseParentheses
--    return $ Formula'UnaryOperator (UnaryOperator'Quantifier q v) f
--    where
--        quantifierOperator :: LParser QuantifierOperator
--        quantifierOperator = 
--            empty
--            <|> (lpSymbol "all" ->> Quantifier'All)
--            <|> (lpSymbol "some" ->> Quantifier'Some)

--formulaNegation :: LParser Formula
--formulaNegation = lpLexeme Negation *> (Formula'UnaryOperator UnaryOperator'Not <$> formulaPredicate)

--formulaWhether :: LParser Formula
--formulaWhether = lpLexeme Whether *> (Formula'UnaryOperator UnaryOperator'Whether <$> formulaPredicate)

--formulaBinary :: LParser Formula
--formulaBinary = pure Formula'BinaryOperator <*> formulaParser <*> operator <*> formulaParser
--    where
--        operator :: LParser BinaryOperator
--        operator = 
--            empty
--            <|> (lpLexeme Disjunction   ->> BinaryOperator'Or           )
--            <|> (lpLexeme Conjunction   ->> BinaryOperator'And          )
--            <|> (lpLexeme Defeats       ->> BinaryOperator'Defeats      )
--            <|> (lpLexeme Conditional   ->> BinaryOperator'Conditional  )
--            <|> (lpLexeme Biconditional ->> BinaryOperator'Biconditional)

--formulaPredicate :: LParser Formula
--formulaPredicate = pure Formula'Predicate <*> predicate <*> many domainFunction
--    where
--        domainFunction :: LParser DomainFunction
--        domainFunction = empty

--formulaParenthetic :: LParser Formula
--formulaParenthetic = openParentheses *> formula <* closeParentheses
-}
