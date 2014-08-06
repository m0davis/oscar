{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.QToken where

import ClassyPrelude

import Oscar.QUBS                       (BinaryOp)
import Oscar.QUBS                       (Quantifier)
import Oscar.QUBS                       (Symbol)
import Oscar.QUBS                       (UnaryOp)

data QToken
    = QTokenUnaryOp !UnaryOp
    | QTokenBinaryOp !BinaryOp
    | QTokenQuantifier !Quantifier
    | QTokenSymbol !Symbol
    deriving (Show)
