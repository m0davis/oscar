{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
module Oscar.FormulaLexer where

import ClassyPrelude hiding (Text, try)

import Control.Applicative
import Control.Monad
import Data.Text.Internal.Lazy (Text)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim hiding ((<|>), many)
import Text.Parsec.String ()
import Text.Parsec.Text.Lazy ()
import Text.Show.Pretty (ppShow)

data Lexeme
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

type TParser = Parsec Text ()

lexemesFromText :: Text -> [Lexeme]
lexemesFromText = either (error . ppShow) id . runParser (many lexeme) () ""

symbolChar :: TParser Char
symbolChar = notFollowedBy space >> notFollowedBy (oneOf "([])") >> anyChar

lexeme :: TParser Lexeme
lexeme = many space *>
    (
        empty
        <|> (char '('                     *> pure OpenParentheses )
        <|> (char '['                     *> pure OpenParentheses )
        <|> (char ')'                     *> pure CloseParentheses)
        <|> (char ']'                     *> pure CloseParentheses)
        <|> (char '~'                     *> pure Negation        )
        <|> (char '?'                     *> pure Whether         )
        <|> try (char 'v'      *> space   *> pure Disjunction     )
        <|> try (char '&'      *> space   *> pure Conjunction     )
        <|> try (string "->"   *> space   *> pure Conditional     )
        <|> try (string "<->"  *> space   *> pure Biconditional   )
        <|> try (char '@'      *> space   *> pure Defeats         )
        <|> try (many1 symbolChar <**> pure (Symbol . pack))
        <|> (many space *> empty)
    )

type LParser = Parsec [Lexeme] ()

lex1 :: Lexeme -> LParser Lexeme
lex1 lexe = token show (const $ initialPos "") $ \ l -> if l == lexe then Just l else Nothing

symbol :: Text -> LParser Lexeme
symbol t = token show (const $ initialPos "") $ \case
    Symbol t -> Just $ Symbol t
    _ -> Nothing

anySymbol :: LParser Lexeme
anySymbol = token show (const $ initialPos "") $ \case
    Symbol text -> Just (Symbol text)
    _ -> Nothing

openParentheses :: LParser Lexeme
openParentheses = token show (const $ initialPos "") $ \case
    OpenParentheses -> Just OpenParentheses
    _ -> Nothing

closeParentheses :: LParser Lexeme
closeParentheses = token show (const $ initialPos "") $ \case
    CloseParentheses -> Just CloseParentheses
    _ -> Nothing

anyLexeme :: LParser Lexeme
anyLexeme = token show (const $ initialPos "") $ \case
    Symbol t -> Just $ Symbol t
    _ -> Nothing
