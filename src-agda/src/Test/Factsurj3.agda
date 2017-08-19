
open import Oscar.Prelude
open import Oscar.Class.Factsurj3
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Leftunit
open import Oscar.Class.HasEquivalence
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

module Test.Factsurj3 where

module Test0
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (_≈'_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  (_◃'_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  test-class' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
  test-class' = !
  test-method' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3.type 𝔓 _≈_ ℜ ε _◃_
  test-method' = Factsurj3.method _ _ _ _ _
  test-class : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → ∀ {x} {p : 𝔓 x} → Leftunit.class (flip (_≈_ {x})) ε _◃_ p
  test-class = !
  test-method : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3.type 𝔓 _≈_ ℜ ε _◃_
  test-method = leftunit
  test' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → ⦃ _ : {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃'_ ⦄ → {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃'_
  test' = !

module Test1
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  test : ⦃ _ : {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
  test = !

module Test2
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  test : ⦃ _ : {_≈_ : ∀̇ π̂² ℓ 𝔓} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → {_≈_ : ∀̇ π̂² ℓ 𝔓} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
  test = !

test-class : ∀
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  → ⦃ _ : 𝓕actsurj3.class 𝔓 ℜ ⦄
  → 𝓕actsurj3.class 𝔓 ℜ
test-class = !
