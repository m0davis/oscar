{-# LANGUAGE NoImplicitPrelude #-}

module Oscar.Formula (
    Formula(..),
    Quantifier(..),
    UnaryOp(..),
    BinaryOp(..),
    Symbol(..),
    Predication(..),
    DomainFunction(..),
  ) where

import ClassyPrelude

data Formula
    = FormulaBinary !BinaryOp !Formula !Formula
    | FormulaUnary !UnaryOp !Formula
    | FormulaQuantification !Quantifier !Symbol !Formula
    | FormulaPredication !Predication
  deriving (Show)

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

data Predication = Predication Symbol [DomainFunction]
  deriving (Show)

data DomainFunction
    = DomainFunction !Symbol ![DomainFunction] -- ^ `g' in (g x)
    | DomainVariable !Symbol                   -- ^ `x' in (g x)
  deriving (Show)
