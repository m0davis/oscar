{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
module Oscar.ProblemDoubleParser where

import ClassyPrelude
import Prelude                          (read)

import Control.Applicative              (many)
import Control.Monad                    (mzero)
import Text.Parsec                      (anyChar)
import Text.Parsec                      (eof)
import Text.Parsec                      (manyTill)
import Text.Parsec                      (space)
import Text.Parsec.Text                 (Parser)

newtype LispPositiveDouble = LispPositiveDouble Double
  deriving (Show)

parserLispPositiveDouble ∷ Parser LispPositiveDouble
parserLispPositiveDouble = do
    d ← many space *> manyTill anyChar ((space *> pure ()) <|> eof)
    if null d then
        mzero
    else
        if headEx d == '.' then
            return . LispPositiveDouble . read $ "0" ++ d
        else if headEx d == '-' then
            error "LispPositiveDouble negative number?"
        else
            return . LispPositiveDouble . read $ d
