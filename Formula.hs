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
import Data.Text.Internal.Lazy      (Text)
import Numeric.Natural              (Natural)
import Text.Parsec.Char             (alphaNum)
import Text.Parsec.Char             (char)
import Text.Parsec.Char             (space)
import Text.Parsec.Char             (string)
import Text.Parsec.Combinator       (many1)
import Text.Parsec.Prim             (try)
import Text.Parsec.Text.Lazy        (Parser)
import Text.Show.Pretty             (ppShow)

import Utilities                    (simpleParse)

-- Parenthesis
data Parenthesis = OpenParenthesis | CloseParenthesis
    deriving (Bounded, Eq, Read, Show)

freeFromParentheses ::
    forall as a b.
    (IsSequence as, Element as ~ a) =>
    (a -> Either Parenthesis b) ->
    as ->
    Free [] b
freeFromParentheses f = fst . ffp 0 []
  where

    ffp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    ffp d prev ass
        | onull ass =
            (Free prev, mempty)
        | Left OpenParenthesis <- f a =
            let (paren, rest) = ffp (succ d) [] as
            in  ffp d (prev ++ [paren]) rest
        | Left CloseParenthesis <- f a
        , d == 0 =
            error "unexpected CloseParenthesis at depth 0"
        | Left CloseParenthesis <- f a =
            (Free prev, as)
        | Right b <- f a =
            ffp d (prev ++ [Pure b]) as
        | otherwise = error ""
          -- suppresses invalid ghc warning about non-exhaustive pattern match
        where
            Just (a, as) = uncons ass

-- QUBS
data Quantifier
    = Universal
    | Existential
    deriving (Show, Eq)

data UnaryOp
    = Negation
    | Whether
    deriving (Show, Eq)

data BinaryOp
    = Conjunction
    | Disjunction
    | Conditional
    | Biconditional
    | Defeater
    deriving (Show, Eq)

newtype Symbol = Symbol Text
    deriving (Show, Eq)

-- module QToken
-- import QToken
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
