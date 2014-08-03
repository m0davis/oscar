{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Formula where

import ClassyPrelude hiding (
    --Text, 
    try,
    )

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
--import Data.Text                    (Text)
--import Data.Text.Internal.Lazy      (Text)
import Text.Show.Pretty             (ppShow)

import Parenthesis                  (freeFromParentheses)
import QUBS                         (Quantifier)
import QUBS                         (UnaryOp)
import QUBS                         (BinaryOp)
import QUBS                         (Symbol)
import QToken                       (QToken(QTokenUnaryOp))
import QToken                       (QToken(QTokenBinaryOp))
import QToken                       (QToken(QTokenQuantifier))
import QToken                       (QToken(QTokenSymbol))
import PQToken                      (makePQTokens)

-- QSToken
-- import QUBS
-- import QToken
data QSToken
    = QSTokenUnaryOp UnaryOp
    | QSTokenBinaryOp BinaryOp
    | QSTokenQuantifier Quantifier Symbol
    | QSTokenSymbol Symbol
    deriving (Show)

makeQSTokenTree :: Free [] QToken -> Free [] QSToken
makeQSTokenTree (Pure (QTokenUnaryOp  u)) = Pure $ QSTokenUnaryOp u
makeQSTokenTree (Pure (QTokenBinaryOp b)) = Pure $ QSTokenBinaryOp b
makeQSTokenTree (Pure (QTokenSymbol   s)) = Pure $ QSTokenSymbol s
makeQSTokenTree (Free [Pure (QTokenQuantifier q), Pure (QTokenSymbol s)])
                                          = Pure $ QSTokenQuantifier q s
makeQSTokenTree (Free ts)                 = Free $ map makeQSTokenTree ts
makeQSTokenTree _ = error "makeQSTokenTree: unexpected QTokenQuantifier"

reformQSTokenTree :: Free [] QSToken -> Free [] QSToken
reformQSTokenTree t@(Pure _) = t
reformQSTokenTree (Free ts) = Free $ reverse . rqstt . reverse $ ts where
    rqstt :: [Free [] QSToken] -> [Free [] QSToken]
    rqstt [] =
        []
    rqstt [a, u@(Pure (QSTokenQuantifier _ _))] =
        [Free [u, reformQSTokenTree a]]
    rqstt (a:u@(Pure (QSTokenUnaryOp _)):as) =
        let chunk = Free [u, reformQSTokenTree a]
        in
            if null as then
                [chunk]
            else
                rqstt (chunk : as)
    rqstt (a:u@(Pure (QSTokenQuantifier _ _)):as) =
        rqstt $ Free [u, reformQSTokenTree a] : as
    rqstt (a:as) =
        reformQSTokenTree a : rqstt as

-- module Formula (DomainFunction(..), Formula(..), Predication(..), makeFormula, makeDomainFunction)
-- import QUBS
-- import QSToken
data Predication = Predication Symbol [DomainFunction]
    deriving (Show)

data DomainFunction
    = DomainFunction Symbol [DomainFunction]
    | DomainVariable Symbol
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
        QuantifierP q s r           -> FormulaQuantification 
            q s (mk r)
        ComplexPredicationP p dfs   -> FormulaPredication $ 
            Predication p $ makeDomainFunction <$> dfs
        SimplePredicationP p        -> FormulaPredication $ 
            Predication p []
        RedundantParenthesesP x -> mk x
        x -> error $ "makeFormula: unexpected structure\n" ++ ppShow x

makeDomainFunction :: Free [] QSToken -> DomainFunction
makeDomainFunction (Pure (QSTokenSymbol s)) =
    DomainVariable s
makeDomainFunction (Free (Pure (QSTokenSymbol s):ss)) =
    DomainFunction s $ map makeDomainFunction ss
makeDomainFunction (Free [x]) =
    makeDomainFunction x
makeDomainFunction x =
    error $ "makeDomainFunction: unexpected structure\n" ++ ppShow x

--
formulaFromText :: Text -> Formula
formulaFromText = id
    . makeFormula
    . reformQSTokenTree
    . makeQSTokenTree
    . freeFromParentheses id
    . makePQTokens
