
open import Oscar.Prelude
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝓼urjectextensivity)
open import Oscar.Data.Proposequality

module Oscar.Class.Factsurj3 where

private

  module _
    {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
    where
    module Visible
      (𝔓 : π̂ 𝔭 𝔛)
      (_≈_ : ∀̇ π̂² ℓ 𝔓) (let infix 4 _≈_; _≈_ = _≈_)
      (ℜ : π̂² 𝔯 𝔛)
      (ε : 𝓻eflexivity ℜ)
      (_◃_ : 𝓼urjectextensivity ℜ 𝔓) (let infix 18 _◃_; _◃_ = _◃_)
      where
      𝓯actsurj3 = λ {x} (p : 𝔓 x) → p ≈ ε ◃ p
      𝒻actsurj3 = ∀ {x} {p : 𝔓 x} → 𝓯actsurj3 p
      record 𝓕actsurj3
        {𝓕 : Ṗroperty ℓ 𝔓}
        ⦃ _ : 𝓕 ≡ ∁ λ p → p ≈ ε ◃ p ⦄
        : Ø 𝔵 ∙̂ 𝔭 ∙̂ ℓ
        where
        field factsurj3 : 𝒻actsurj3
      Factsurj3 : Ø _
      Factsurj3 = 𝓕actsurj3 ⦃ ∅ ⦄
      factsurj3⟦_/_/_/_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
      factsurj3⟦_/_/_/_/_⟧ ⦃ I ⦄ = 𝓕actsurj3.factsurj3 I
    module Hidden
      {𝔓 : π̂ 𝔭 𝔛}
      {_≈_ : ∀̇ π̂² ℓ 𝔓}
      {ℜ : π̂² 𝔯 𝔛}
      {ε : 𝓻eflexivity ℜ}
      {_◃_ : 𝓼urjectextensivity ℜ 𝔓}
      where
      open Visible 𝔓 _≈_ ℜ ε _◃_
      factsurj3 : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
      factsurj3 = factsurj3⟦_/_/_/_/_⟧

open Visible public
open Hidden public
