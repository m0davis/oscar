{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
-----------------------------------------------------------------------------
-- |
--   Description : import me
--   Copyright   : (C) 2004, Oleg Kiselyov, Ralf Laemmel, Keean Schupke
--
--   The HList library
--
--   This module re-exports everything needed to use HList.
--
-- You can derive lenses automatically for many data types:
--
-- @
-- import Control.Lens
-- data Foo a = Foo { _fooArgs :: ['String'], _fooValue :: a }
-- 'makeLenses' ''Foo
-- @
--
-- This defines the following lenses:
-- 
-- > (++) = mappend
-- | > (++) = mappend
module Oscar.Formula ( 
    -- * header
    -- ** subheader
    -- | the \"public\" parts. More examples are in the module documentation.
    Predication(..),
    Formula(..),
    pattern BinaryOpP,
    -- * functionswtf
    makeFormula,
    -- ** subssubfunctions
    formulaFromText,            
    )
    where

import ClassyPrelude hiding (
    try,
    )

import Control.Monad.Free               (Free(Free))
import Control.Monad.Free               (Free(Pure))
import Text.Show.Pretty                 (ppShow)

import Oscar.DomainFunction             (DomainFunction)
import Oscar.DomainFunction             (makeDomainFunction)
import Oscar.Parenthesis                (freeFromParentheses)
import Oscar.PQToken                    (makePQTokens)
import Oscar.QSToken                    (makeQSTokenTree)
import Oscar.QSToken                    (QSToken(QSTokenBinaryOp))
import Oscar.QSToken                    (QSToken(QSTokenQuantifier))
import Oscar.QSToken                    (QSToken(QSTokenSymbol))
import Oscar.QSToken                    (QSToken(QSTokenUnaryOp))
import Oscar.QSToken                    (reformQSTokenTree)
import Oscar.QUBS                       (BinaryOp)
import Oscar.QUBS                       (Quantifier)
import Oscar.QUBS                       (Symbol)
import Oscar.QUBS                       (UnaryOp)

data Predication = Predication Symbol [DomainFunction]
    deriving (Show)

data Formula
    = FormulaBinary !BinaryOp !Formula !Formula
    | FormulaUnary !UnaryOp !Formula
    | FormulaQuantification !Quantifier !Symbol !Formula
    | FormulaPredication !Predication
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

-- You can derive lenses automatically for many data types:
--
-- @
-- import Control.Lens
-- data Foo a = Foo { _fooArgs :: ['String'], _fooValue :: a }
-- 'makeLenses' ''Foo
-- @
--
-- This defines the following lenses:
-- | > (++) = mappend
makeFormula :: Free [] QSToken -> Formula
makeFormula = mk . traceShowId
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



{- $label6demo #label6demo#

 Instances from "Data.HList.Label6"

>>> :set -XDataKinds
>>> (Label :: Label "x") .=. (5::Int) .*. emptyRecord
Record{x=5}

>>> let x = Label :: Label "x"
>>> let r = x .=. (5::Int) .*. emptyRecord
>>> r .!. x
5

-}
formulaFromText :: Text -> Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens
    . traceShowId
