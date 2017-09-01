
open import Oscar.Prelude
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Leftunit
open import Oscar.Class.HasEquivalence
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆
open import Oscar.Class.Surjection

module Test.Factsurj3 where

module Test0
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (_≈'_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : Surjectextensivity.type ℜ 𝔓)
  (_◃'_ : Surjectextensivity.type ℜ 𝔓)
  where
  test-class' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_ ⦄ → Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_
  test-class' = !
  test-method' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_ ⦄ → Factsurj3.type 𝔓 _≈_ ℜ ε surjection _◃_
  test-method' = leftunit
  test-class : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_ ⦄ → ∀ {x} {p : 𝔓 x} → Leftunit.class (flip (_≈_ {x})) ε _◃_ p
  test-class = !
  test-method : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε surjection _◃_ ⦄ → Factsurj3.type 𝔓 _≈_ ℜ ε surjection _◃_
  test-method = leftunit

test-class : ∀
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  → ⦃ _ : 𝓕actsurj3.class 𝔓 ℜ ⦄
  → 𝓕actsurj3.class 𝔓 ℜ
test-class = !
