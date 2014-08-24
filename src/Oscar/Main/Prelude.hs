{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A convenient Prelude, used by all modules in this system.
-}

module Oscar.Main.Prelude (
    module ClassyPrelude,
    ppShow,
    ClassyPrelude.undefined,
    (⊥),
    type (⁞),
    ƭ,
    unƭ,
    reƭ,
    empty,
    many,
    mzero,
    guardM,
    liftA2,
    (<=<),
    Free(..),
    Natural,
    ppPrint,
    ) where

import ClassyPrelude hiding (
    try,
    undefined,
    )
import Prelude                          (undefined)

import Text.Show.Pretty                 (ppShow)

import qualified ClassyPrelude

import Data.Tagged                      (Tagged(Tagged))
import Data.Tagged                      (unTagged)
import Data.Tagged                      (retag)
import Control.Conditional              (guardM)
import Control.Applicative              (empty)
import Control.Applicative              (many)
import Control.Applicative              (liftA2)
import Control.Monad                    ((<=<))
import Control.Monad                    (mzero)
import Control.Monad.Free               (Free(Free))
import Control.Monad.Free               (Free(Pure))
import Numeric.Natural                  (Natural)

(⊥) ∷ a
(⊥) = undefined

type a ⁞ b = Tagged b a

ƭ ∷ a → a ⁞ b
ƭ = Tagged

unƭ ∷ a ⁞ b → a
unƭ = unTagged

reƭ ∷ a ⁞ b → a ⁞ c
reƭ = retag

ppPrint ∷ (Show a) => a → IO ()
ppPrint = putStrLn . pack . ppShow
