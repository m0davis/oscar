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
reformQSTokenTree (Free ts) = Free $ reverse . suo . reverse $ ts where
    suo :: [Free [] QSToken] -> [Free [] QSToken]
    suo [] = 
        []
    suo [a, u@(Pure (QSTokenQuantifier _ _))] =
        [Free [u, reformQSTokenTree a]]
    suo (a:u@(Pure (QSTokenUnaryOp _)):as) =
        let chunk = Free [u, reformQSTokenTree a] 
        in 
            if null as then
                [chunk]
            else
                suo (chunk : as)
    suo (a:u@(Pure (QSTokenQuantifier _ _)):as) =
        suo $ Free [u, reformQSTokenTree a] : as
    suo (a:as) = 
        reformQSTokenTree a : suo as

--
data Predication = Predication Symbol [DomainFunction]
    deriving (Show)

data DomainFunction 
    = DomainFunction Symbol [DomainFunction]
    | DomainVariable Symbol
    deriving (Show)

-- Formula
data Formula
    = FormulaBinary BinaryOp Formula Formula
    | FormulaUnary UnaryOp Formula
    | FormulaQuantification Quantifier Symbol Formula
    | FormulaPredication Predication
    deriving (Show)

formula :: Free [] QSToken -> Formula
formula (Free [l,Pure (QSTokenBinaryOp b), r]) = 
    FormulaBinary b (formula l) (formula r)
formula (Free [Pure (QSTokenUnaryOp u), r]) = 
    FormulaUnary u (formula r)
formula (Free [Pure (QSTokenQuantifier q s), r]) = 
    FormulaQuantification q s (formula r)
formula (Free (Pure (QSTokenSymbol s):ss)) = 
    FormulaPredication $ Predication s $ domainFunction <$> ss
formula (Pure (QSTokenSymbol s)) = 
    FormulaPredication $ Predication s []
formula (Free [x]) = 
    formula x
formula x = 
    error ("formula: unexpected structure: \n" ++ ppShow x)

domainFunction :: Free [] QSToken -> DomainFunction
domainFunction (Pure (QSTokenSymbol s)) = 
        DomainVariable s
domainFunction (Free (Pure (QSTokenSymbol s):ss)) = 
        DomainFunction s $ map domainFunction ss
domainFunction (Free [x]) = 
        domainFunction x
domainFunction _ = 
        error "domainFunction: unexpected structure"

--
formulaFromText :: Text -> Formula
formulaFromText = id
    . formula 
    . reformQSTokenTree 
    . qsFromQTokenTree 
    . freeFromParentheses id 
    . pqTokensFromText
