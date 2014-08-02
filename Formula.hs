{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Formula where

import Text.Show.Pretty (ppShow)
--import Debug.Trace (traceShow)

import ClassyPrelude hiding (Text, try)

import Control.Applicative
import Control.Lens hiding (uncons)
import Control.Monad
import Control.Monad.Free
import Data.Either.Utils (maybeToEither)
import Data.List.Split
import Data.Pointed
import Data.Text.Internal.Lazy (Text)
import Numeric.Natural
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Pos
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
freeFromParentheses f = fst . tfp 0 []
    where

    tfp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    tfp d prev ass
        | onull ass =
            (Free prev, mempty)
        | Left OpenParenthesis <- f a =
            let (paren, rest) = tfp (succ d) [] as
            in  tfp d (prev ++ [paren]) rest
        | Left CloseParenthesis <- f a
        , d == 0 =
            error "unexpected CloseParenthesis at depth 0"
        | Left CloseParenthesis <- f a =
            (Free prev, as)
        | Right b <- f a =
            tfp d (prev ++ [Pure b]) as
        where
            Just (a, as) = uncons ass

-- QUBS
data Quantifier
    = Universal
    | Existential
    deriving (Show, Eq)

data UnaryOperator
    = Negation
    | Whether
    deriving (Show, Eq)

data BinaryOperator
    = Conjunction
    | Disjunction
    | Conditional
    | Biconditional
    | Defeater
    deriving (Show, Eq)

newtype Symbol = Symbol Text
    deriving (Show, Eq)

-- QToken
data QToken
    =   QTokenUnaryOperator UnaryOperator
    |   QTokenBinaryOperator BinaryOperator
    |   QTokenQuantifier Quantifier
    |   QTokenSymbol Symbol
    deriving (Show)

atoken :: Parser (Either Parenthesis QToken)
atoken = empty
    <|> Left                         <$> parenthesis   
    <|> Right . QTokenUnaryOperator  <$> unaryOperator 
    <|> Right . QTokenBinaryOperator <$> binaryOperator
    <|> Right . QTokenQuantifier     <$> quantifier    
    <|> Right . QTokenSymbol         <$> symbol        
  where
    p **> v = try p *> pure v

    parenthesis = empty
        <|> char '('            **> OpenParenthesis
        <|> char '['            **> OpenParenthesis
        <|> char ')'            **> CloseParenthesis
        <|> char ']'            **> CloseParenthesis

    unaryOperator = empty
        <|> char '?'            **> Whether 
        <|> char '~'            **> Negation

    binaryOperator = empty
        <|> (char 'v' >> space) **> Disjunction  
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
    =   QSTokenUnaryOperator UnaryOperator
    |   QSTokenBinaryOperator BinaryOperator
    |   QSTokenQuantifier Quantifier Symbol
    |   QSTokenSymbol Symbol
    deriving (Show)

bTokenTree :: Free [] QToken -> Free [] QSToken
bTokenTree (Pure (QTokenUnaryOperator  u)) = Pure $ QSTokenUnaryOperator u
bTokenTree (Pure (QTokenBinaryOperator b)) = Pure $ QSTokenBinaryOperator b
bTokenTree (Pure (QTokenSymbol         s)) = Pure $ QSTokenSymbol s
bTokenTree (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)]) 
                                           = Pure $ QSTokenQuantifier q s
bTokenTree (Free ts)                       = Free $ map bTokenTree ts

structurePrefixOperators :: Free [] QSToken -> Free [] QSToken
structurePrefixOperators t@(Pure _) = t
structurePrefixOperators (Free ts) = Free $ reverse . suo . reverse $ ts where
    suo :: [Free [] QSToken] -> [Free [] QSToken]
    suo [] = 
        []
    suo [a, u@(Pure (QSTokenQuantifier _ _))] =
        [Free [u, structurePrefixOperators a]]
    suo (a:u@(Pure (QSTokenUnaryOperator _)):as) =
        let chunk = Free [u, structurePrefixOperators a] 
        in 
            if null as then
                [chunk]
            else
                suo (chunk : as)
    suo (a:u@(Pure (QSTokenQuantifier _ _)):as) =
        suo $ Free [u, structurePrefixOperators a] : as
    suo (a:as) = 
        structurePrefixOperators a : suo as

-- Formula
data Formula
    = FormulaBinary BinaryOperator Formula Formula
    | FormulaUnary UnaryOperator Formula
    | FormulaQuantification Quantifier Symbol Formula
    | FormulaPredication Symbol [Free [] Symbol]
    deriving (Show)

formula :: Free [] QSToken -> Formula
formula (Free [l,Pure (QSTokenBinaryOperator b), r]) = 
        FormulaBinary b (formula l) (formula r)
formula (Free [Pure (QSTokenUnaryOperator u), r]) = 
        FormulaUnary u (formula r)
formula (Free [Pure (QSTokenQuantifier q s), r]) = 
        FormulaQuantification q s (formula r)
formula (Free (Pure (QSTokenSymbol s):ss)) = 
        FormulaPredication s $ map subformula ss
    where
    subformula :: Free [] QSToken -> Free [] Symbol
    subformula (Pure (QSTokenSymbol s)) = 
            Pure s
    subformula (Free (Pure (QSTokenSymbol s):ss)) = 
            Free (Pure s:map subformula ss)
    subformula _ = 
            error "subformula: unexpected structure"
formula (Pure (QSTokenSymbol s)) = 
        FormulaPredication s []
formula (Free [x]) = 
        formula x
formula x = 
        error ("formula: unexpected structure: \n" ++ ppShow x)

--
formulaFromText :: Text -> Formula
formulaFromText = formula . structurePrefixOperators . bTokenTree . freeFromParentheses id . simpleParse (many (many space *> atoken))
