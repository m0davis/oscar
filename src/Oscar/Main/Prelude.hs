{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{- | A convenient Prelude, used by all modules in this system.
-}

module Oscar.Main.Prelude (
    -- * "ClassyPrelude"
    -- $ClassyPrelude
    module ClassyPrelude,
    ClassyPrelude.undefined,
    (⊥),
    -- * "Control.Lens"
    -- $Control.Lens
    module Control.Lens,
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
    snoc,
    try,
    undefined,
    )
import Prelude                          (undefined)
import qualified ClassyPrelude

import qualified Control.Lens hiding (
    snoc,
    )

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

{- TODO Report a haddock bug. 

The below narratives should be placed in the source above the relevant import
statements, but doing so triggers an error in haddock.
-}

{- $ClassyPrelude

There is a name conflict between 'ClassyPrelude.try' (from "ClassyPrelude")
and 'Text.Parsec.try' (from "Text.Parsec"). We don't need to do any 
exception handling, so, for the moment, we are simply hiding the one from
ClassyPrelude.

TODO We will eventually have the need for exception-handling. Come up with
a convenient way to include ClassyPrelude.try.

There is also a name conflict between 'ClassyPrelude.snoc' (ClassyPrelude) 
and 'Control.Lens.Cons.snoc' (Control.Lens). We don't need either of these, 
so, for the moment, we simply hide both of them!

TODO Decide what to do with snoc once the need arrives for one of them.
-}

{- $Control.Lens

Everything but 'Control.Lens.Cons.snoc'.
-}

-- | Bottom. Use this to avoid the warning from 'ClassyPrelude.undefined'
(⊥) ∷ a
(⊥) = undefined

-- | A wrapper around 'ppShow'
ppPrint ∷ (Show a) ⇒ a → IO ()
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
