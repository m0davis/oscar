{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Oscar.Formula where

import ClassyPrelude hiding (
    try,
    )

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
import Text.Show.Pretty             (ppShow)

import Oscar.Parenthesis            (freeFromParentheses)
import Oscar.QUBS                   (Quantifier)
import Oscar.QUBS                   (UnaryOp)
import Oscar.QUBS                   (BinaryOp)
import Oscar.QUBS                   (Symbol)
import Oscar.PQToken                (makePQTokens)
import Oscar.QSToken                (QSToken(QSTokenUnaryOp))
import Oscar.QSToken                (QSToken(QSTokenBinaryOp))
import Oscar.QSToken                (QSToken(QSTokenQuantifier))
import Oscar.QSToken                (QSToken(QSTokenSymbol))
import Oscar.QSToken                (makeQSTokenTree)
import Oscar.QSToken                (reformQSTokenTree)
import Oscar.DomainFunction         (DomainFunction)
import Oscar.DomainFunction         (makeDomainFunction)

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
