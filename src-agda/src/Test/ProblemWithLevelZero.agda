{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.ProblemWithLevelZero where

module _ (𝔓 : Ø₀) where

  open Substitunction 𝔓
  open Term 𝔓

  fails : ∀ {m n} (f : Substitunction m n) → Substitunction m n
  fails f = transitivity f ε -- FIXME

  refl-works : ∀ {m} → Substitunction m m
  refl-works = ε

  transitivity-hole : ∀ {m n} (f : Substitunction m n) → Substitunction m n
  transitivity-hole f =
    transitivity
      ⦃ {!!!} -- FIXME does not resolve instance
        ⦄
      f
      {!!}
