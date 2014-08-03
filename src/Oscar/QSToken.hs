{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.QSToken where

import ClassyPrelude

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))

import Oscar.QUBS                         (Quantifier)
import Oscar.QUBS                         (UnaryOp)
import Oscar.QUBS                         (BinaryOp)
import Oscar.QUBS                         (Symbol)
import Oscar.QToken                       (QToken(QTokenUnaryOp))
import Oscar.QToken                       (QToken(QTokenBinaryOp))
import Oscar.QToken                       (QToken(QTokenQuantifier))
import Oscar.QToken                       (QToken(QTokenSymbol))

data QSToken
    = QSTokenUnaryOp !UnaryOp
    | QSTokenBinaryOp !BinaryOp
    | QSTokenQuantifier !Quantifier !Symbol
    | QSTokenSymbol !Symbol
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
