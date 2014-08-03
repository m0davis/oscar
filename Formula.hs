{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Formula where

import Text.Show.Pretty (ppShow)

import ClassyPrelude hiding (Text, try)

import Control.Applicative
import Control.Monad.Free
import Data.Text.Internal.Lazy (Text)
import Numeric.Natural
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim hiding ((<|>), many, uncons)
import Text.Parsec.String ()
import Text.Parsec.Text.Lazy

import Utilities

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

-- QToken and PQToken
data QToken
    = QTokenUnaryOp UnaryOp
    | QTokenBinaryOp BinaryOp
    | QTokenQuantifier Quantifier
    | QTokenSymbol Symbol
    deriving (Show)

type PQToken = Either Parenthesis QToken

pqTokensFromText :: Text -> [PQToken]
pqTokensFromText = simpleParse (many (many space *> parsePQToken))
  where
    parsePQToken :: Parser PQToken
    parsePQToken = empty
        <|> Left                         <$> parenthesis
        <|> Right . QTokenUnaryOp  <$> unaryOp
        <|> Right . QTokenBinaryOp <$> binaryOp
        <|> Right . QTokenQuantifier     <$> quantifier
        <|> Right . QTokenSymbol         <$> symbol
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
data QSToken
    = QSTokenUnaryOp UnaryOp
    | QSTokenBinaryOp BinaryOp
    | QSTokenQuantifier Quantifier Symbol
    | QSTokenSymbol Symbol
    deriving (Show)

qsFromQTokenTree :: Free [] QToken -> Free [] QSToken
qsFromQTokenTree (Pure (QTokenUnaryOp  u)) = Pure $ QSTokenUnaryOp u
qsFromQTokenTree (Pure (QTokenBinaryOp b)) = Pure $ QSTokenBinaryOp b
qsFromQTokenTree (Pure (QTokenSymbol   s)) = Pure $ QSTokenSymbol s
qsFromQTokenTree (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)])
                                           = Pure $ QSTokenQuantifier q s
qsFromQTokenTree (Free ts)                 = Free $ map qsFromQTokenTree ts
qsFromQTokenTree _ = error "qsFromQTokenTree: unexpected QTokenQuantifier"

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

-- Formula
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



--formulaFromQSTokenTree :: Free [] QSToken -> Formula
--formulaFromQSTokenTree (Free [l,Pure (QSTokenBinaryOp b), r]) =
--    FormulaBinary b (formulaFromQSTokenTree l) (formulaFromQSTokenTree r)
--formulaFromQSTokenTree (Free [Pure (QSTokenUnaryOp u), r]) =
--    FormulaUnary u (formulaFromQSTokenTree r)
--formulaFromQSTokenTree (Free [Pure (QSTokenQuantifier q s), r]) =
--    FormulaQuantification q s (formulaFromQSTokenTree r)
--formulaFromQSTokenTree (Free (Pure (QSTokenSymbol s):ss)) =
--    FormulaPredication $ Predication s $ domainFunctionFromQSTokenTree <$> ss
--formulaFromQSTokenTree (Pure (QSTokenSymbol s)) =
--    FormulaPredication $ Predication s []
--formulaFromQSTokenTree (Free [x]) =
--    formulaFromQSTokenTree x
--formulaFromQSTokenTree x =
--    error $ "formulaFromQSTokenTree: unexpected structure\n" ++ ppShow x

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

formulaFromQSTokenTree :: Free [] QSToken -> Formula
formulaFromQSTokenTree = make
  where
    make = \case
        BinaryOpP l o r             -> FormulaBinary 
            o (make l) (make r)
        UnaryOpP o r                -> FormulaUnary 
            o (make r)
        QuantifierP q s r           -> FormulaQuantification 
            q s (make r)
        ComplexPredicationP p dfs   -> FormulaPredication $ 
            Predication p $ domainFunctionFromQSTokenTree <$> dfs
        SimplePredicationP p        -> FormulaPredication $ 
            Predication p []
        RedundantParenthesesP x -> make x
        x -> error $ "formulaFromQSTokenTree: unexpected structure\n" ++ ppShow x

domainFunctionFromQSTokenTree :: Free [] QSToken -> DomainFunction
domainFunctionFromQSTokenTree (Pure (QSTokenSymbol s)) =
    DomainVariable s
domainFunctionFromQSTokenTree (Free (Pure (QSTokenSymbol s):ss)) =
    DomainFunction s $ map domainFunctionFromQSTokenTree ss
domainFunctionFromQSTokenTree (Free [x]) =
    domainFunctionFromQSTokenTree x
domainFunctionFromQSTokenTree x =
    error $ "domainFunctionFromQSTokenTree: unexpected structure\n" ++ ppShow x

--
formulaFromText :: Text -> Formula
formulaFromText = id
    . formulaFromQSTokenTree
    . reformQSTokenTree
    . qsFromQTokenTree
    . freeFromParentheses id
    . pqTokensFromText
