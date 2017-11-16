{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --show-implicit #-}

open import Oscar.Prelude
open import Oscar.Class

-- classes
open import Oscar.Class.Transitivity

-- data
open import Oscar.Data.Substitunction
open import Oscar.Data.Term

module Test.EquivalentCandidates-2 where

module _
  {a}
  where

  instance

    𝓣ransitivityFunction₁ : Transitivity.class Function⟦ a ⟧
    𝓣ransitivityFunction₁ .⋆ f g = g ∘ f

    𝓣ransitivityFunction₂ : Transitivity.class Function⟦ a ⟧
    𝓣ransitivityFunction₂ .⋆ f g = g ∘ f

module _ (𝔓 : Ø₀) where

  open Substitunction 𝔓
  open Term 𝔓

  test-1 test-2 test-3 test-4 test-5 test-6 :
    ∀ {m n} (f : Substitunction m n) → Substitunction m n

  test-1 f = transitivity {!!} {!!}
  test-2 f = transitivity {𝔒 = Ø₀} {_∼_ = Function⟦ ∅̂ ⟧} {!!} {!!}
  test-3 f = transitivity f {!!}
  test-4 {m} {n} f = transitivity {𝔒 = Ø₀} f (¡ {𝔒 = Term n})
  test-5 f = transitivity {_∼_ = Function⟦ ∅̂ ⟧} f {!!}
  test-6 {m} {n} f = transitivity {𝔒 = Ø₀} ⦃ {!!} ⦄ f (¡ {𝔒 = Term n})
