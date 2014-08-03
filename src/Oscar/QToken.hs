{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.QToken where

import ClassyPrelude

import Oscar.QUBS                   (Quantifier)
import Oscar.QUBS                   (UnaryOp)
import Oscar.QUBS                   (BinaryOp)
import Oscar.QUBS                   (Symbol)

data QToken
    = QTokenUnaryOp !UnaryOp
    | QTokenBinaryOp !BinaryOp
    | QTokenQuantifier !Quantifier
    | QTokenSymbol !Symbol
    deriving (Show)
