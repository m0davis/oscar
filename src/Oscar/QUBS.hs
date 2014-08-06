{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.QUBS where

import ClassyPrelude

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
