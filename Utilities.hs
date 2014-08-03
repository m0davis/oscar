{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Utilities where

import ClassyPrelude hiding (
    --Text, 
    try,
    )
import Text.Show.Pretty (ppShow)

import Control.Applicative
import Control.Conditional hiding (unlessM)
import Control.Monad
import Control.Monad.Free
import Data.Either.Utils (maybeToEither)
import Data.Pointed
--import Data.Text.Internal.Lazy (Text)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim hiding ((<|>), many, uncons)
import Text.Parsec.String ()
--import Text.Parsec.Text.Lazy
import Text.Parsec.Text

simplify :: Free [] a -> Free [] a
simplify (Free [a]) = simplify a
simplify (Free as)  = Free $ map simplify as
simplify (Pure a)   = Pure a

eitherOr ::
    a ->
    (a -> Maybe b) ->
    Either a b
eitherOr a f = maybeToEither a (f a)

mconcatRightPoints ::
    (Pointed p, Semigroup s, p r ~ s) =>
    [Either l r] ->
    [Either l s]
mconcatRightPoints [] = []
mconcatRightPoints (Left l : xs) = Left l : mconcatRightPoints xs
mconcatRightPoints (Right r : xs) = case mconcatRightPoints xs of
    (Right rs : ys) -> Right (point r <> rs) : ys
    ys              -> Right (point r      ) : ys

joinFree :: Functor f => Free f (f a) -> Free f a
joinFree (Pure as) = Free (map Pure as)
joinFree (Free fs) = Free $ map joinFree fs

--
simpleParse :: Parser a -> Text -> a
simpleParse p = either (error . ppShow) id . runParser p () ""

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

precededBy :: Parser p1 -> Parser p2 -> Parser (p1, p2)
precededBy p1 p2 = do
    firstInput <- pack <$> manyTill anyChar (lookAhead . try $ p2)
    liftA2 (,) (withInput firstInput p1) p2

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
