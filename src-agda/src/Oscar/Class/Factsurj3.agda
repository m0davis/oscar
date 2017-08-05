
open import Oscar.Prelude
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝒮urjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

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
      (_◃_ : 𝒮urjectextensivity ℜ 𝔓) (let infix 18 _◃_; _◃_ = _◃_)
      where
      𝓯actsurj3 = λ {x} (p : 𝔓 x) → p ≈ ε ◃ p
      𝒻actsurj3 = ∀ {x} {p : 𝔓 x} → 𝓯actsurj3 p
      Factsurj3 : Ø _
      Factsurj3 = ∀ {x} → Leftunit (flip (_≈_ {x})) (ε {x}) _◃_
      factsurj3⟦_/_/_/_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
      factsurj3⟦_/_/_/_/_⟧ = leftunit
    module _
      where
      open import Oscar.Class.HasEquivalence
      open import Oscar.Class.Reflexivity
      open import Oscar.Class.Surjectextensivity
      module Principal
        (𝔓 : π̂ 𝔭 𝔛)
        ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
        (ℜ : π̂² 𝔯 𝔛)
        ⦃ _ : 𝓡eflexivity ℜ ⦄
        ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
        where
        open Visible 𝔓 _≈_ ℜ ε surjectextensivity
        [Factsurj3] = Factsurj3
        factsurj3⟦_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
        factsurj3⟦_/_⟧ = factsurj3⟦_/_/_/_/_⟧

open Visible public
open Principal public
