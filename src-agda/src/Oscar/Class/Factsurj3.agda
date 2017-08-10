
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝒮urjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

open import Oscar.Class.Leftunit

module Oscar.Class.Factsurj3 where

module Factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  class = ∀ {x} {p : 𝔓 x} → $ClassSingle.class (flip (_≈_ {x})) (ε {x}) _◃_ p
  type = ∀ {x} {p : 𝔓 x} → $ClassSingle.type (flip (_≈_ {x})) (ε {x}) _◃_ p
  method = λ ⦃ _ : class ⦄ {x} {p : 𝔓 x} → $ClassSingle.method (flip (_≈_ {x})) (ε {x}) _◃_ p

module factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛}
  {ε : 𝓻eflexivity ℜ}
  {_◃_ : 𝒮urjectextensivity ℜ 𝔓}
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
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  where
  class = Factsurj3.class 𝔓 _≈_ ℜ ε surjectextensivity
  type = Factsurj3.type 𝔓 _≈_ ℜ ε surjectextensivity
  method = Factsurj3.method 𝔓 _≈_ ℜ ε surjectextensivity

module 𝓯actsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  where
  method = 𝓕actsurj3.method 𝔓 ℜ ⦃ ! ⦄ ⦃ ! ⦄
