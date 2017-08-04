
open import Oscar.Prelude
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝓼urjectextensivity)
open import Oscar.Data.Constraint

open import Oscar.Class.Leftunit

module Oscar.Class.Factsurj3 where

open import Oscar.Class.Leftunit using (𝓛eftunit) public

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
      Factsurj3 : Ø _
      Factsurj3 = ∀ {x} → Leftunit (flip (_≈_ {x})) (ε {x}) _◃_
      factsurj3⟦_/_/_/_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
      factsurj3⟦_/_/_/_/_⟧ = leftunit
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
