
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝒮urjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

open import Oscar.Class.Leftunit

module Oscar.Class.Factsurj3 where

module Factsurj3Interface0
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  {x}
  (p : 𝔓 x)
  where
  open LeftunitInterface0 (flip (_≈_ {x})) (ε {x}) _◃_ p public

module Factsurj3Interface1
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  open Factsurj3Interface0 𝔓 _≈_ ℜ ε _◃_
  Factsurj3 = ∀ {x} {p : 𝔓 x} → GET-CLASS p
  𝒻actsurj3 = ∀ {x} {p : 𝔓 x} → SET-METHOD p
  factsurj3⟦_/_/_/_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
  factsurj3⟦_/_/_/_/_⟧ = leftunit

open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity

module Factsurj3Interface2
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  (ℜ : π̂² 𝔯 𝔛)
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  where
  open Factsurj3Interface1 𝔓 _≈_ ℜ ε surjectextensivity
  [Factsurj3] = Factsurj3
  factsurj3⟦_/_⟧ : ⦃ _ : Factsurj3 ⦄ → 𝒻actsurj3
  factsurj3⟦_/_⟧ = factsurj3⟦_/_/_/_/_⟧

open Factsurj3Interface1 public
open Factsurj3Interface2 public
