{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.PQToken where

import ClassyPrelude hiding (
    try,
    )

import Control.Applicative              (empty)
import Control.Applicative              (many)
import Text.Parsec.Char                 (alphaNum)
import Text.Parsec.Char                 (char)
import Text.Parsec.Char                 (space)
import Text.Parsec.Char                 (string)
import Text.Parsec.Combinator           (many1)
import Text.Parsec.Prim                 (try)
import Text.Parsec.Text                 (Parser)

import Oscar.Parenthesis                (Parenthesis(CloseParenthesis))
import Oscar.Parenthesis                (Parenthesis(OpenParenthesis))
import Oscar.QToken                     (QToken(QTokenBinaryOp))
import Oscar.QToken                     (QToken(QTokenQuantifier))
import Oscar.QToken                     (QToken(QTokenSymbol))
import Oscar.QToken                     (QToken(QTokenUnaryOp))
import Oscar.QUBS                       (BinaryOp(Biconditional))
import Oscar.QUBS                       (BinaryOp(Conditional))
import Oscar.QUBS                       (BinaryOp(Conjunction))
import Oscar.QUBS                       (BinaryOp(Defeater))
import Oscar.QUBS                       (BinaryOp(Disjunction))
import Oscar.QUBS                       (Quantifier(Existential))
import Oscar.QUBS                       (Quantifier(Universal))
import Oscar.QUBS                       (Symbol(Symbol))
import Oscar.QUBS                       (UnaryOp(Negation))
import Oscar.QUBS                       (UnaryOp(Whether))
import Oscar.Utilities                  (simpleParse)

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
