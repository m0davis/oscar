{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --show-implicit #-}

open import Oscar.Prelude
open import Oscar.Class

-- classes
open import Oscar.Class.Transitivity

-- data
open import Oscar.Data.Substitunction
open import Oscar.Data.Term

module Test.EquivalentCandidates where

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

  non-unique non-unique-2-hole unique-1-hole unsolved-meta :
    ∀ {m n} (f : Substitunction m n) → Substitunction m n
  non-unique {m} {n} f = {!transitivity {𝔒 = Ø₀} f (¡ {𝔒 = Term n})!}
  {-
  Candidates:
    [ 𝓣ransitivityFunction₁ : {a : Ł} → Transitivity.class Function⟦ a ⟧
    , 𝓣ransitivityFunction₂ : {a : Ł} → Transitivity.class Function⟦ a ⟧ ]
  -}
  non-unique-2-hole f = {!transitivity {𝔒 = Ø₀} {!!} {!!}!}
  {-
  Candidates:
    [ 𝓣ransitivityFunction₁ : {a : Ł} → Transitivity.class Function⟦ a ⟧
    , 𝓣ransitivityFunction₂ : {a : Ł} → Transitivity.class Function⟦ a ⟧ ]
  -}
  unique-1-hole f = transitivity {_∼_ = Function} f {!!}
  unsolved-meta {m} {n} f = transitivity {𝔒 = Ø₀} ⦃ {!!} ⦄ f (¡ {𝔒 = Term n})
