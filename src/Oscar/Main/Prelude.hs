{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Oscar.Main.Prelude (
    module ClassyPrelude,
    ppShow,
    ClassyPrelude.undefined,
    (⊥),
    type (⁞),
    ƭ,
    unƭ,        
    empty,
    many,
    mzero,
    guardM,
    liftA2,
    (<=<),
    Free(..),
    Natural,
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

ƭ ∷ a → Tagged b a
ƭ = Tagged

unƭ ∷ Tagged b a → a
unƭ = unTagged
