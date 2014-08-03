{-# LANGUAGE NoImplicitPrelude #-}
module Oscar.DomainFunction where

import ClassyPrelude

import Control.Monad.Free           (Free(Free))
import Control.Monad.Free           (Free(Pure))
import Text.Show.Pretty             (ppShow)

import Oscar.QUBS                   (Symbol)
import Oscar.QSToken                (QSToken(QSTokenSymbol))

-- | A DomainFunction represents 
data DomainFunction
    = DomainFunction !Symbol ![DomainFunction] -- ^ `g' in (g x)
    | DomainVariable !Symbol                   -- ^ `x' in (g x)
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
