{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.ProblemWithLevelZero where

module _ (𝔓 : Ø₀) where

  open Substitunction 𝔓

  test-level-0 : ∀ {m n} (f : Substitunction m n) → Substitunction m n
  test-level-0 f = transitivity f ε -- FIXME
