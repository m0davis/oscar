{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Formula where

import ClassyPrelude hiding (
    try,
    )

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
import Text.Show.Pretty             (ppShow)

import Parenthesis                  (freeFromParentheses)
import QUBS                         (Quantifier)
import QUBS                         (UnaryOp)
import QUBS                         (BinaryOp)
import QUBS                         (Symbol)
import PQToken                      (makePQTokens)
import QSToken                      (QSToken(QSTokenUnaryOp))
import QSToken                      (QSToken(QSTokenBinaryOp))
import QSToken                      (QSToken(QSTokenQuantifier))
import QSToken                      (QSToken(QSTokenSymbol))
import QSToken                      (makeQSTokenTree)
import QSToken                      (reformQSTokenTree)
import DomainFunction               (DomainFunction)
import DomainFunction               (makeDomainFunction)

data Predication = Predication Symbol [DomainFunction]
    deriving (Show)

data Formula
    = FormulaBinary BinaryOp Formula Formula
    | FormulaUnary UnaryOp Formula
    | FormulaQuantification Quantifier Symbol Formula
    | FormulaPredication Predication
    deriving (Show)


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

makeFormula :: Free [] QSToken -> Formula
makeFormula = mk
  where
    mk = \case
        BinaryOpP l o r             -> FormulaBinary 
            o (mk l) (mk r)
        UnaryOpP o r                -> FormulaUnary 
            o (mk r)
        QuantifierP q v f           -> FormulaQuantification 
            q v (mk f)
        ComplexPredicationP p dfs   -> FormulaPredication $ 
            Predication p $ makeDomainFunction <$> dfs
        SimplePredicationP p        -> FormulaPredication $ 
            Predication p []
        RedundantParenthesesP f -> mk f
        x -> error $ "makeFormula: unexpected structure\n" ++ ppShow x


--
formulaFromText :: Text -> Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens
