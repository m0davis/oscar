{-# LANGUAGE NoImplicitPrelude #-}
module QToken where

import ClassyPrelude

import QUBS                         (Quantifier)
import QUBS                         (UnaryOp)
import QUBS                         (BinaryOp)
import QUBS                         (Symbol)

data QToken
    = QTokenUnaryOp UnaryOp
    | QTokenBinaryOp BinaryOp
    | QTokenQuantifier Quantifier
    | QTokenSymbol Symbol
    deriving (Show)


