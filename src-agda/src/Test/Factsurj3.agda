
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
  (_◃_ : Smaphomarrow!.type ℜ 𝔓)
  (_◃'_ : Smaphomarrow!.type ℜ 𝔓)
  where
  test-class' : ⦃ _ : Leftunit,smaphomarrow.class ℜ 𝔓 ε surjection _◃_ _≈_ ⦄ → Leftunit,smaphomarrow.class ℜ 𝔓 ε surjection _◃_ _≈_
  test-class' = !
  test-method' : ⦃ _ : Leftunit,smaphomarrow.class ℜ 𝔓 ε surjection _◃_ _≈_ ⦄ → Leftunit,smaphomarrow.type ℜ 𝔓 ε surjection _◃_ _≈_
  test-method' = leftunit

test-class : ∀
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  → ⦃ _ : Leftunit,equivalence,smaphomarrow!.class ℜ 𝔓 ⦄
  → Leftunit,equivalence,smaphomarrow!.class ℜ 𝔓
test-class = !
