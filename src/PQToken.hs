{-# LANGUAGE NoImplicitPrelude #-}
module PQToken where

import ClassyPrelude hiding (
    try,
    )

import Control.Applicative          (empty)
import Control.Applicative          (many)
import Text.Parsec.Char             (alphaNum)
import Text.Parsec.Char             (char)
import Text.Parsec.Char             (space)
import Text.Parsec.Char             (string)
import Text.Parsec.Combinator       (many1)
import Text.Parsec.Prim             (try)
import Text.Parsec.Text             (Parser)

import Parenthesis                  (Parenthesis(OpenParenthesis))
import Parenthesis                  (Parenthesis(CloseParenthesis))
import QUBS                         (Quantifier(Universal))
import QUBS                         (Quantifier(Existential))
import QUBS                         (UnaryOp(Negation))
import QUBS                         (UnaryOp(Whether))
import QUBS                         (BinaryOp(Conjunction))
import QUBS                         (BinaryOp(Disjunction))
import QUBS                         (BinaryOp(Conditional))
import QUBS                         (BinaryOp(Biconditional))
import QUBS                         (BinaryOp(Defeater))
import QUBS                         (Symbol(Symbol))
import QToken                       (QToken(QTokenUnaryOp))
import QToken                       (QToken(QTokenBinaryOp))
import QToken                       (QToken(QTokenQuantifier))
import QToken                       (QToken(QTokenSymbol))
import Utilities                    (simpleParse)

type PQToken = Either Parenthesis QToken

makePQTokens :: Text -> [PQToken]
makePQTokens = simpleParse $ many $ many space *> parsePQToken
  where
    parsePQToken :: Parser PQToken
    parsePQToken = empty
        <|> Left                     <$> parenthesis
        <|> Right . QTokenUnaryOp    <$> unaryOp
        <|> Right . QTokenBinaryOp   <$> binaryOp
        <|> Right . QTokenQuantifier <$> quantifier
        <|> Right . QTokenSymbol     <$> symbol
      where
        p **> v = try p *> pure v
        infixl 4 **>

        parenthesis = empty
            <|> char '('            **> OpenParenthesis
            <|> char '['            **> OpenParenthesis
            <|> char ')'            **> CloseParenthesis
            <|> char ']'            **> CloseParenthesis

        unaryOp = empty
            <|> char '?'            **> Whether
            <|> char '~'            **> Negation

        binaryOp = empty
            <|> char 'v' *> space   **> Disjunction
            <|> char '&'            **> Conjunction
            <|> char '@'            **> Defeater
            <|> string "->"         **> Conditional
            <|> string "<->"        **> Biconditional

        quantifier = empty
            <|> string "all"        **> Universal
            <|> string "some"       **> Existential

        symbol = Symbol . pack <$> many1 alphaNum
