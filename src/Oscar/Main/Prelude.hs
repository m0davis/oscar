{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A convenient Prelude, used by all modules in this system.
-}

module Oscar.Main.Prelude (
    -- * "ClassyPrelude"
    module ClassyPrelude,
    ClassyPrelude.undefined,
    (⊥),
    -- * "Text.Show.Pretty"
    ppShow,
    ppPrint,
    -- * "Data.Tagged"
    type (⁞),
    ƭ,
    unƭ,
    reƭ,
    -- * "Control.Applicative"
    empty,
    many,
    liftA2,
    -- * "Control.Monad"
    mzero,
    (<=<),
    -- * "Control.Conditional"
    guardM,
    -- * "Control.Monad.Free"
    Free(..),
    -- * "Numeric.Natural"
    Natural,
    ) where

import ClassyPrelude hiding (
    try,
    undefined,
    )
import Prelude                          (undefined)

import qualified ClassyPrelude

import Control.Applicative              (empty)
import Control.Applicative              (liftA2)
import Control.Applicative              (many)
import Control.Conditional              (guardM)
import Control.Monad                    ((<=<))
import Control.Monad                    (mzero)
import Control.Monad.Free               (Free(Free))
import Control.Monad.Free               (Free(Pure))
import Data.Tagged                      (Tagged(Tagged))
import Data.Tagged                      (retag)
import Data.Tagged                      (unTagged)
import Numeric.Natural                  (Natural)
import Text.Show.Pretty                 (ppShow)

-- | Bottom. Use this to avoid the warning from 'ClassyPrelude.undefined'
(⊥) ∷ a
(⊥) = undefined

-- | A wrapper around 'ppShow'
ppPrint ∷ (Show a) => a → IO ()
ppPrint = putStrLn . pack . ppShow

type a ⁞ b = Tagged b a

-- | 'Tagged'
ƭ ∷ a → a ⁞ b
ƭ = Tagged

-- | 'unTagged'
unƭ ∷ a ⁞ b → a
unƭ = unTagged

-- | 'retag'
reƭ ∷ a ⁞ b → a ⁞ c
reƭ = retag
