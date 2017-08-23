
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (module Surjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

open import Oscar.Class.Leftunit
open import Oscar.Data.𝟙

module Oscar.Class.Factsurj3 where

module Factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : Surjectextensivity.TYPE ℜ 𝔓)
  = ℭLASS ((λ {x} → ε {x}) , (λ {x y} → _◃_ {x} {y}) , (λ {x} → _≈_ {x})) (∀ {x} {p : 𝔓 x} → p ≈ (ε ◃ p))

module _
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛}
  {ε : 𝓻eflexivity ℜ}
  {_◃_ : Surjectextensivity.TYPE ℜ 𝔓}
  ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄
  where
  instance
    unprimeFactsurj3 : ∀ {x} {p : 𝔓 x} → Leftunit.class (flip (_≈_ {x})) ε _◃_ p
    unprimeFactsurj3 .⋆ = Factsurj3.method 𝔓 _≈_ ℜ ε _◃_

module factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛}
  {ε : 𝓻eflexivity ℜ}
  {_◃_ : Surjectextensivity.TYPE ℜ 𝔓}
  where
  method = Factsurj3.method 𝔓 _≈_ ℜ ε _◃_

open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity

module 𝓕actsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  (ℜ : π̂² 𝔯 𝔛)
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  = Factsurj3 𝔓 _≈_ ℜ ε surjectextensivity

module 𝓯actsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  where
  method = 𝓕actsurj3.method 𝔓 ℜ ⦃ ! ⦄ ⦃ ! ⦄
