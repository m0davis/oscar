
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
    ⦃ isEquivalence ⦄ : IsEquivalence _≈_

open Equivalence ⦃ … ⦄ public

open import Foundation.Bottom

infix 4 _≉_
_≉_ : ∀ {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ ⦃ _ : ∀ {x} → Bottom ℓ x  ⦄ → A → A → Set ℓ
x ≉ y =  x ≈ y → ⊥ {{!!}} {{!!}}

-- record EquivalenceWithNegation {a} (A : Set a) ℓ ⦃ _ : ∀ {b} → Bottom b ⦄ : ℞ a ⊔ ⟰ ℓ where
--   field
--     ⦃ equivalence ⦄ : Equivalence A ℓ

--   infix 4 _≉_
--   _≉_ : A → A → Set ℓ
--   _≉_ = {!!}

-- -- module NegEquiv {ℓ'} (⊥ : Set ℓ') ⦃ _ : ∀ {b} → IsBottom ⊥ b ⦄ where

-- --   _≉_ : ∀ {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → A → A → Set (ℓ ⊔ ℓ')
-- --   x ≉ y = x ≈ y → ⊥
