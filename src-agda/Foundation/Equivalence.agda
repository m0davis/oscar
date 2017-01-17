
module Foundation.Equivalence where

open import Foundation.Primitive

record IsEquivalence {a} {A : Set a} {ℓ} (_≈_ : A → A → Set ℓ) : ℞ a ⊔ ℓ where
  field
    reflexivity : ∀ x → x ≈ x
    symmetry : ∀ x y → x ≈ y → y ≈ x
    transitivity : ∀ x y z → x ≈ y → y ≈ z → x ≈ z

open IsEquivalence ⦃ … ⦄ public

record Equivalence {a} (A : Set a) ℓ : ℞ a ⊔ ⟰ ℓ where
  infix 4 _≈_
  field
    _≈_ : A → A → Set ℓ
    instance ⦃ isEquivalence ⦄ : IsEquivalence _≈_

open Equivalence ⦃ … ⦄ public

open import Foundation.Bottom

infix 4 _≉_
_≉_ : ∀ {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ {b} ⦃ _ : Bottom b ℓ  ⦄ → A → A → Set (b ⊔ ℓ)
_≉_ {ℓ = ℓ} x y = ¬ (x ≈ y)
