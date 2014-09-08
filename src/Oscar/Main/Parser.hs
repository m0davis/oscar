{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A convenient import for modules that otherwise would need "Text.Parsec".
-}

module Oscar.Main.Parser (
    -- * "Prelude"
    read,
    -- * "Text.Parsec.Text"
    Parser,
    -- * "Text.Parsec"
    ParsecT,
    Stream,
    alphaNum,
    anyChar,
    char,
    eof,
    getInput,
    lookAhead,
    many1,
    manyTill,
    newline,
    notFollowedBy,
    option,
    runParser,
    setInput,
    skipMany,
    space,
    spaces,
    string,
    try,
    -- * Custom parser functions
    simpleParse,
    manyTillBefore,
    skipManyTill,
    skipManyTillBefore,
    precededBy,
    withInput,
    nonNewlineSpace,
    spacesUpToEndOfLine,
    spacesUpToEof,
    apparentlyAloneOnLine,
    definitelyAloneOnLine,
    ) where

import Oscar.Main.Prelude

import Prelude                          (read)
import Text.Parsec                      (alphaNum)
import Text.Parsec                      (anyChar)
import Text.Parsec                      (char)
import Text.Parsec                      (eof)
import Text.Parsec                      (getInput)
import Text.Parsec                      (lookAhead)
import Text.Parsec                      (many1)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (newline)
import Text.Parsec                      (notFollowedBy)
import Text.Parsec                      (option)
import Text.Parsec                      (ParsecT)
import Text.Parsec                      (Stream)
import Text.Parsec                      (runParser)
import Text.Parsec                      (setInput)
import Text.Parsec                      (skipMany)
import Text.Parsec                      (space)
import Text.Parsec                      (spaces)
import Text.Parsec                      (string)
import Text.Parsec                      (try)
import Text.Parsec.Text                 (Parser)

-- | Mainly, a wrapper around 'runParser'.
simpleParse ∷ Parser a → Text → a
simpleParse p = either (error . ppShow) id . runParser p () ""

{- manyTillBefore p end applies parser p zero or more times until parser
   end succeeds, stopping just ahead of end.
-}
manyTillBefore ∷ (Stream s m t)
    ⇒ ParsecT s u m a
    → ParsecT s u m end
    → ParsecT s u m [a]
manyTillBefore p end = manyTill p (lookAhead . try $ end)

{- skipManyTill p end applies parser p zero or more times until parser end
   succeeds, skipping its result.
-}
skipManyTill ∷ (Stream s m t)
    ⇒ ParsecT s u m a
    → ParsecT s u m end
    → ParsecT s u m ()
skipManyTill p end = manyTillBefore p end *> end *> pure ()

{- skipManyTillBefore p end applies parser p zero or more times until parser
   end succeeds, skipping the p\'s, and stopping just ahead of end.
-}
skipManyTillBefore ∷ (Stream s m t)
    ⇒ ParsecT s u m a
    → ParsecT s u m end
    → ParsecT s u m ()
skipManyTillBefore p end = manyTillBefore p end *> pure ()

{- | precededBy p1 p2 finds the first place where p2 succeeds, then runs p1 on
     the text up to (but not including) that that place.
-}
precededBy ∷ Parser p1 → Parser p2 → Parser (p1, p2)
precededBy p1 p2 = do
    firstInput ← pack <$> manyTill anyChar (lookAhead . try $ p2)
    liftA2 (,) (withInput firstInput p1) p2

{- | withInput stream parser runs parser on the given stream, without
     affecting the current input state of the parser in which it is used.
-}
withInput ∷ Monad m ⇒ s → ParsecT s u m a → ParsecT s u m a
withInput s p = do
    s' ← getInput
    setInput s
    p' ← p
    setInput s'
    return p'

{- | nonNewlineSpace consumes only a 'space' that is not a 'newline'. -}
nonNewlineSpace ∷ Stream s m Char ⇒ ParsecT s u m Char
nonNewlineSpace = notFollowedBy newline *> space

{- | spacesUpToEndOfLine consumes the whitespace preceding a 'newline' or
     'eof'. If non-whitespace characters are found, the parser fails and does
     not consume anything.
-}
spacesUpToEndOfLine ∷ Stream s m Char ⇒ ParsecT s u m [Char]
spacesUpToEndOfLine = try $
    manyTillBefore nonNewlineSpace $ eof <|> (newline *> pure ())

{- | spacesUpToEof consumes the whitespace before an 'eof'. If non-whitespace
     characters are found, the parser fails and does not consume anything.
-}
spacesUpToEof ∷ Stream s m Char ⇒ ParsecT s u m [Char]
spacesUpToEof = try $
    manyTillBefore nonNewlineSpace eof

{- | apparentlyAloneOnLine p successfully applies parser p only if it is
     immediately followed by whitespace up to the next 'newline' or 'eof'.
     Upon success, it returns the parsed result without consuming the
     following whitespace. Otherwise, nothing is consumed.
-}
apparentlyAloneOnLine ∷ Stream s m Char ⇒ ParsecT s u m a → ParsecT s u m a
apparentlyAloneOnLine p = try $
    p <* lookAhead spacesUpToEndOfLine

{- | definitelyAloneOnLine p first ensures that there is an upcoming newline
     not preceded by any anything but whitespace. At the first non-whitespace
     it then applies parser 'apparentlyAloneOnLine' p. If any parse fails,
     nothing is consumed. If it succeeds, the parser consumes only the
     preceding whitespace and p.
-}
definitelyAloneOnLine ∷ Stream s m Char ⇒ ParsecT s u m a → ParsecT s u m a
definitelyAloneOnLine p = try $
    spacesUpToEndOfLine *>
    newline *>
    skipMany nonNewlineSpace *>
    apparentlyAloneOnLine p
