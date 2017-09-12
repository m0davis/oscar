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

  solution-1o solution-1a solution-2o solution-2a :
    ∀ {m n} (f : Substitunction m n) → Substitunction m n

  solution-1o f = transitivity {𝔒 = ¶} f ε
  solution-1a f = transitivity[ Substitunction ] f ε
  solution-2o f = {!transitivity {𝔒 = Ø₀} f ε!}
  solution-2a f = {!transitivity[ Function ] f ε!}

  transitivity-hole : ∀ {m n} (f : Substitunction m n) → Substitunction m n
  transitivity-hole f =
    transitivity
      ⦃ ! -- FIXME does not resolve instance
        ⦄
      f
      {!!}
    {-
      Candidates
        TransitivityFunction : {𝔬 : Ł} → Transitivity.class Function⟦ 𝔬 ⟧
        𝓣ransitivitySubstitunction :
          {𝔭 : Ł} {𝔓 = 𝔓₁ : Ø 𝔭} →
          Transitivity.class (Substitunction.Substitunction 𝔓₁)
    -}
