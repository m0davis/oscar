
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (module Surjectextensivity)
open import Oscar.Data.Constraint
open import Oscar.Class.Surjection

open import Oscar.Class.Leftunit
open import Oscar.Data.𝟙

module Oscar.Class.Factsurj3 where

module Factsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔓 : π̂ 𝔭 𝔛₂)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛₁)
  (ε : 𝓻eflexivity ℜ)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  (_◃_ : Surjectextensivity.type ℜ 𝔓 ⦃ ∁ surjection ⦄)
  = ℭLASS ((λ {x} → ε {x}) , (λ {x y} → _◃_ {x} {y}) , (λ {x} → _≈_ {x}))
          (∀ {x} {p : 𝔓 (surjection x)} → p ≈ (ε ◃ p))

module _
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {𝔓 : π̂ 𝔭 𝔛₂}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛₁}
  {ε : 𝓻eflexivity ℜ}
  {surjection : Surjection.type 𝔛₁ 𝔛₂}
  {_◃_ : Surjectextensivity.type ℜ 𝔓 ⦃ ∁ surjection ⦄}
  ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_ ⦄
  where
  instance
    unprimeFactsurj3 : ∀ {x} {p : 𝔓 (surjection x)} → Leftunit.class (flip (_≈_ {surjection x})) ε _◃_ p
    unprimeFactsurj3 .⋆ = Factsurj3.method 𝔓 _≈_ ℜ ε surjection _◃_

module factsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {𝔓 : π̂ 𝔭 𝔛₂}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛₁}
  {ε : 𝓻eflexivity ℜ}
  {surjection : Surjection.type 𝔛₁ 𝔛₂}
  {_◃_ : Surjectextensivity.type ℜ 𝔓 ⦃ ∁ surjection ⦄}
  where
  method = Factsurj3.method 𝔓 _≈_ ℜ ε surjection _◃_

open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity

module 𝓕actsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  (ℜ : π̂² 𝔯 𝔛₁)
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  = Factsurj3 𝔓 _≈_ ℜ ε surjection surjectextensivity

module 𝓯actsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {𝔓 : π̂ 𝔭 𝔛₂}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛₁}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  where
  method = 𝓕actsurj3.method 𝔓 ℜ ⦃ ! ⦄ ⦃ ! ⦄
