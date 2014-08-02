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

data Parenthesis = OpenParenthesis | CloseParenthesis
    deriving (Bounded, Eq, Read, Show)

treeFromParentheses ::
    forall as a b.
    (IsSequence as, Element as ~ a) =>
    (a -> Either Parenthesis b) ->
    as ->
    Free [] b
treeFromParentheses f = fst . tfp 0 []
    where

    tfp :: Natural -> [Free [] b] -> as -> (Free [] b, as)
    tfp d prev ass
        |   onull ass =
                (Free prev, mempty)
        |   otherwise =
                case f a of
                    Left OpenParenthesis ->
                        let (paren, rest) = tfp (succ d) [] as
                        in  tfp d (prev ++ [paren]) rest
                    Left CloseParenthesis ->
                        case d of
                            0 -> error "unexpected CloseParenthesis at depth 0"
                            _ -> (Free prev, as)
                    Right b -> -- ^?! _Right
                        tfp d (prev ++ [Pure b]) as
        where
            Just (a, as) = uncons ass

data Quantifier
    =   Quantifier_Universal
    |   Quantifier_Existential
    deriving (Show, Eq)

data UnaryOperator
    =   UnaryOperator_Negation
    |   UnaryOperator_Whether
    deriving (Show, Eq)

data BinaryOperator
    =   BinaryOperator_Conjunction
    |   BinaryOperator_Disjunction
    |   BinaryOperator_Conditional
    |   BinaryOperator_Biconditional
    |   BinaryOperator_Defeater
    deriving (Show, Eq)

data AToken
    =   ATokenUnaryOperator UnaryOperator
    |   ATokenBinaryOperator BinaryOperator
    |   ATokenQuantifier Quantifier
    |   ATokenSymbol Text
    deriving (Show)

atoken :: Parser (Either Parenthesis AToken)
atoken = many space *> do empty
    <|> Left                         <$> parenthesis   
    <|> Right . ATokenUnaryOperator  <$> unaryOperator 
    <|> Right . ATokenBinaryOperator <$> binaryOperator
    <|> Right . ATokenQuantifier     <$> quantifier    
    <|> Right . ATokenSymbol . pack  <$> symbol        
  where
    p **> v = try p *> pure v

    parenthesis = empty
        <|> char '(' **> OpenParenthesis
        <|> char '[' **> OpenParenthesis
        <|> char ')' **> CloseParenthesis
        <|> char ']' **> CloseParenthesis

    unaryOperator = empty
        <|> char '?' **> UnaryOperator_Whether 
        <|> char '~' **> UnaryOperator_Negation

    binaryOperator = empty
        <|> (char 'v' >> space) **> BinaryOperator_Disjunction  
        <|> char '&'            **> BinaryOperator_Conjunction  
        <|> char '@'            **> BinaryOperator_Defeater     
        <|> string "->"         **> BinaryOperator_Conditional  
        <|> string "<->"        **> BinaryOperator_Biconditional

    quantifier = empty
        <|> string "all"        **> Quantifier_Universal  
        <|> string "some"       **> Quantifier_Existential
        
    symbol = many1 alphaNum

data BToken
    =   BTokenUnaryOperator UnaryOperator
    |   BTokenBinaryOperator BinaryOperator
    |   BTokenQuantifier Quantifier Text
    |   BTokenSymbol Text
    deriving (Show)

bTokenTree :: Free [] AToken -> Free [] BToken
bTokenTree (Pure (ATokenUnaryOperator u)) = Pure (BTokenUnaryOperator u)
bTokenTree (Pure (ATokenBinaryOperator b)) = Pure (BTokenBinaryOperator b)
bTokenTree (Pure (ATokenSymbol s)) = Pure (BTokenSymbol s)
bTokenTree (Free [Pure (ATokenQuantifier q), Pure (ATokenSymbol s)]) = Pure (BTokenQuantifier q s)
bTokenTree (Free ts) = Free $ map bTokenTree ts

structurePrefixOperators :: Free [] BToken -> Free [] BToken
structurePrefixOperators t@(Pure _) = t
structurePrefixOperators (Free ts) = Free $ reverse . suo . reverse $ ts where
    suo :: [Free [] BToken] -> [Free [] BToken]
    suo [] = []
    suo [a, u@(Pure (BTokenQuantifier _ _))] =
        [Free [u, structurePrefixOperators a]]
    suo (a:u@(Pure (BTokenUnaryOperator _)):as) =
        let chunk = Free [u, structurePrefixOperators a] 
        in 
            if null as then
                [chunk]
            else
                suo (chunk:as)
    suo (a:u@(Pure (BTokenQuantifier _ _)):as) =
        suo $ Free [u, structurePrefixOperators a]:as
    suo (a:as) = structurePrefixOperators a:suo as

data Formula
    =   FormulaBinary BinaryOperator Formula Formula
    |   FormulaUnary UnaryOperator Formula
    |   FormulaQuantification Quantifier Text Formula
    |   FormulaPredication Text [Free [] Text]
    deriving (Show)

pattern Binary b l r = (Free [l,Pure (BTokenBinaryOperator b), r])

formula :: Free [] BToken -> Formula
formula (Binary b l r) = FormulaBinary b (formula l) (formula r)
formula (Free [Pure (BTokenUnaryOperator u), r]) = FormulaUnary u (formula r)
formula (Free [Pure (BTokenQuantifier q s), r]) = FormulaQuantification q s (formula r)
formula (Free (Pure (BTokenSymbol s):ss)) = FormulaPredication s (map subformula ss)
    where
    subformula :: Free [] BToken -> Free [] Text
    subformula (Pure (BTokenSymbol s)) = Pure s
    subformula (Free (Pure (BTokenSymbol s):ss)) = Free (Pure s:map subformula ss)
    subformula _ = error "subformula: unexpected structure"
formula (Pure (BTokenSymbol s)) = FormulaPredication s []
formula (Free [x]) = formula x
formula x = error ("formula: unexpected structure: \n" ++ ppShow x)

formulaFromText :: Text -> Formula
formulaFromText = formula . structurePrefixOperators . bTokenTree . treeFromParentheses id . simpleParse (many atoken)
