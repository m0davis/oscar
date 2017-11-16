
open import Oscar.Prelude

module Oscar.Data.¶ where

data ¶ : Set where
  ∅ : ¶
  ↑_  : ¶ → ¶

{-# BUILTIN NATURAL ¶ #-}

Nat = ¶

record ℕ : Ø₀ where
  constructor ↑_
  field ⋆ : ¶
