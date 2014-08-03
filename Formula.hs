{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Formula where

import ClassyPrelude hiding (
    Text, 
    try,
    )

import Control.Applicative          (empty)
import Control.Applicative          (many)
import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
import Data.Text                    (Text)
--import Data.Text.Internal.Lazy      (Text)
import Text.Parsec.Char             (alphaNum)
import Text.Parsec.Char             (char)
import Text.Parsec.Char             (space)
import Text.Parsec.Char             (string)
import Text.Parsec.Combinator       (many1)
import Text.Parsec.Prim             (try)
--import Text.Parsec.Text.Lazy        (Parser)
import Text.Parsec.Text             (Parser)
import Text.Show.Pretty             (ppShow)

import Utilities                    (simpleParse)
import Parenthesis                  (freeFromParentheses)
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

-- module QToken
-- import QToken
-- import QUBS
data QToken
    = QTokenUnaryOp UnaryOp
    | QTokenBinaryOp BinaryOp
    | QTokenQuantifier Quantifier
    | QTokenSymbol Symbol
    deriving (Show)


-- PQToken
-- import Parenthesis (Parenthesis)
-- import QToken
-- import QUBS
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

-- QSToken
-- import QUBS
-- import QToken
data QSToken
    = QSTokenUnaryOp UnaryOp
    | QSTokenBinaryOp BinaryOp
    | QSTokenQuantifier Quantifier Symbol
    | QSTokenSymbol Symbol
    deriving (Show)

makeQSTokenTree :: Free [] QToken -> Free [] QSToken
makeQSTokenTree (Pure (QTokenUnaryOp  u)) = Pure $ QSTokenUnaryOp u
makeQSTokenTree (Pure (QTokenBinaryOp b)) = Pure $ QSTokenBinaryOp b
makeQSTokenTree (Pure (QTokenSymbol   s)) = Pure $ QSTokenSymbol s
makeQSTokenTree (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)])
                                          = Pure $ QSTokenQuantifier q s
makeQSTokenTree (Free ts)                 = Free $ map makeQSTokenTree ts
makeQSTokenTree _ = error "makeQSTokenTree: unexpected QTokenQuantifier"

reformQSTokenTree :: Free [] QSToken -> Free [] QSToken
reformQSTokenTree t@(Pure _) = t
reformQSTokenTree (Free ts) = Free $ reverse . rqstt . reverse $ ts where
    rqstt :: [Free [] QSToken] -> [Free [] QSToken]
    rqstt [] =
        []
    rqstt [a, u@(Pure (QSTokenQuantifier _ _))] =
        [Free [u, reformQSTokenTree a]]
    rqstt (a:u@(Pure (QSTokenUnaryOp _)):as) =
        let chunk = Free [u, reformQSTokenTree a]
        in
            if null as then
                [chunk]
            else
                rqstt (chunk : as)
    rqstt (a:u@(Pure (QSTokenQuantifier _ _)):as) =
        rqstt $ Free [u, reformQSTokenTree a] : as
    rqstt (a:as) =
        reformQSTokenTree a : rqstt as

-- module Formula (DomainFunction(..), Formula(..), Predication(..), makeFormula, makeDomainFunction)
-- import QUBS
-- import QSToken
data Predication = Predication Symbol [DomainFunction]
    deriving (Show)

data DomainFunction
    = DomainFunction Symbol [DomainFunction]
    | DomainVariable Symbol
    deriving (Show)

data Formula
    = FormulaBinary BinaryOp Formula Formula
    | FormulaUnary UnaryOp Formula
    | FormulaQuantification Quantifier Symbol Formula
    | FormulaPredication Predication
    deriving (Show)


pattern BinaryOpP left op right 
        = Free [left,Pure (QSTokenBinaryOp op), right]

pattern UnaryOpP op right 
        = Free [Pure (QSTokenUnaryOp op), right]

pattern QuantifierP quantifier variable formula
        = Free [Pure (QSTokenQuantifier quantifier variable), formula]

pattern ComplexPredicationP predication domainFunctions
        = Free (Pure (QSTokenSymbol predication):domainFunctions)

pattern SimplePredicationP predication     
        = Pure (QSTokenSymbol predication)

pattern RedundantParenthesesP x
        = Free [x]

makeFormula :: Free [] QSToken -> Formula
makeFormula = mk
  where
    mk = \case
        BinaryOpP l o r             -> FormulaBinary 
            o (mk l) (mk r)
        UnaryOpP o r                -> FormulaUnary 
            o (mk r)
        QuantifierP q s r           -> FormulaQuantification 
            q s (mk r)
        ComplexPredicationP p dfs   -> FormulaPredication $ 
            Predication p $ makeDomainFunction <$> dfs
        SimplePredicationP p        -> FormulaPredication $ 
            Predication p []
        RedundantParenthesesP x -> mk x
        x -> error $ "makeFormula: unexpected structure\n" ++ ppShow x

makeDomainFunction :: Free [] QSToken -> DomainFunction
makeDomainFunction (Pure (QSTokenSymbol s)) =
    DomainVariable s
makeDomainFunction (Free (Pure (QSTokenSymbol s):ss)) =
    DomainFunction s $ map makeDomainFunction ss
makeDomainFunction (Free [x]) =
    makeDomainFunction x
makeDomainFunction x =
    error $ "makeDomainFunction: unexpected structure\n" ++ ppShow x

--
formulaFromText :: Text -> Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens
