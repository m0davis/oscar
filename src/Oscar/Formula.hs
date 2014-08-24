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

import Oscar.Main.Prelude

data Formula
    = FormulaBinary !BinaryOp !Formula !Formula
    | FormulaUnary !UnaryOp !Formula
    | FormulaQuantification !Quantifier !Symbol !Formula
    | FormulaPredication !Predication
  deriving (Eq, Read, Show)

data Quantifier
    = Universal    -- ^ (all ...)
    | Existential  -- ^ (some ...)
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data UnaryOp
    = Negation  -- ^ ~
    | Whether   -- ^ ?
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data BinaryOp
    = Conjunction   -- ^ &
    | Disjunction   -- ^ v
    | Conditional   -- ^ \->
    | Biconditional -- ^ \<->
    | Defeater      -- ^ @
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

newtype Symbol = Symbol Text
  deriving (Eq, Read, Show)

data Predication = Predication Symbol [DomainFunction]
  deriving (Eq, Read, Show)

data DomainFunction
    = DomainFunction !Symbol ![DomainFunction] -- ^ `g' in P (g x)
    | DomainVariable !Symbol                   -- ^ `x' or `y' in P (g x) y
  deriving (Eq, Read, Show)
