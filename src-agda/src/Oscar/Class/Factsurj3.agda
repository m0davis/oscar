
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝒮urjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

open import Oscar.Class.Leftunit

module Oscar.Class.Factsurj3 where

module Fact3Class
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  {x}
  (p : 𝔓 x)
  where
  open Leftunit (flip (_≈_ {x})) (ε {x}) _◃_ p public

module Fact3Interface
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  open Fact3Class 𝔓 _≈_ ℜ ε _◃_ public

module Factsurj3Interface1
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  private module ∁ = Fact3Interface 𝔓 _≈_ ℜ ε _◃_
  𝒄lass = ∀ {x} {p : 𝔓 x} → ∁.𝒄lass p
  𝓽ype = ∀ {x} {p : 𝔓 x} → ∁.𝒕ype p
  𝒎ethod : ⦃ _ : 𝒄lass ⦄ → 𝓽ype
  𝒎ethod {p = p} = ∁.𝒎ethod p

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
  private module ∁ = Factsurj3Interface1 𝔓 _≈_ ℜ ε surjectextensivity
  𝒄lass = ∁.𝒄lass
  𝓽ype = ∁.𝓽ype
  𝒎ethod : ⦃ _ : 𝒄lass ⦄ → 𝓽ype
  𝒎ethod = ∁.𝒎ethod
