{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Main.Parser (
    alphaNum,
    anyChar,
    char,
    eof,
    lookAhead,
    space,
    spaces,
    string,
    manyTill,
    many1,
    option,
    try,
    notFollowedBy,
    Parser,
    simpleParse,
    precededBy,
    withInput,
    read,
    ) where

import Oscar.Main.Prelude

import Prelude                          (read)
import Text.Parsec.Char                 (alphaNum)
import Text.Parsec.Char                 (char)
import Text.Parsec.Char                 (space)
import Text.Parsec.Char                 (spaces)
import Text.Parsec.Char                 (string)
import Text.Parsec.Combinator           (many1)
import Text.Parsec.Prim                 (try)
import Text.Parsec.Text                 (Parser)
import Text.Parsec                      (anyChar)
import Text.Parsec                      (eof)
import Text.Parsec                      (lookAhead)
import Text.Parsec                      (option)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (getInput)
import Text.Parsec                      (notFollowedBy)
import Text.Parsec                      (setInput)
import Text.Parsec                      (runParser)
import Text.Parsec                      (ParsecT)

simpleParse :: Parser a -> Text -> a
simpleParse p = either (error . ppShow) id . runParser p () ""

precededBy :: Parser p1 -> Parser p2 -> Parser (p1, p2)
precededBy p1 p2 = do
    firstInput <- pack <$> manyTill anyChar (lookAhead . try $ p2)
    liftA2 (,) (withInput firstInput p1) p2

withInput :: Monad m => s -> ParsecT s u m a -> ParsecT s u m a
withInput s p = do
    s' <- getInput
    setInput s
    p' <- p
    setInput s'
    return p'
