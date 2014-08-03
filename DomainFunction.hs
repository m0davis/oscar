{-# LANGUAGE NoImplicitPrelude #-}
module DomainFunction where

import ClassyPrelude

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
import Text.Show.Pretty             (ppShow)

import QUBS                         (Symbol)
import QSToken                      (QSToken(QSTokenSymbol))

data DomainFunction
    = DomainFunction Symbol [DomainFunction]
    | DomainVariable Symbol
    deriving (Show)

makeDomainFunction :: Free [] QSToken -> DomainFunction
makeDomainFunction (Pure (QSTokenSymbol s)) =
    DomainVariable s
makeDomainFunction (Free (Pure (QSTokenSymbol s):ss)) =
    DomainFunction s $ map makeDomainFunction ss
makeDomainFunction (Free [x]) =
    makeDomainFunction x
makeDomainFunction x =
    error $ "makeDomainFunction: unexpected structure\n" ++ ppShow x

