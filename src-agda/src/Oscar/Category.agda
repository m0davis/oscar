
module Oscar.Category where

open import Oscar.Prelude using (it)

open import Level

import Relation.Binary as B
open import Algebra

record Equality {a} (A : Set a) ℓ : Set (a ⊔ suc ℓ) where
  infix 4 _≋_
  field
    _≋_ : A → A → Set ℓ
    isEquivalence : B.IsEquivalence _≋_

open Equality ⦃ … ⦄ using (_≋_)

module RelationBinaryMorphismCore where

  Rel : ∀ {o} {O : Set o} {m} → B.Rel O m → ∀ ℓ → Set (o ⊔ m ⊔ suc ℓ)
  Rel _⊸_ ℓ = ∀ {x y} → x ⊸ y → x ⊸ y → Set ℓ

  Associative : ∀ {o m ℓ} {O : Set o} (⊸ : B.Rel O m) → B.TransitiveFlip ⊸ → Rel ⊸ ℓ → Set _
  Associative _⊸_ _∙_ _≈_ = ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≈ (h ∙ (g ∙ f))

  _/_Preserves₂_⟶_⟶_ :
    ∀ {o m ℓ₁ ℓ₂ ℓ₃} {O : Set o} (⊸ : B.Rel O m)
    (∙ : B.TransitiveFlip ⊸)
    (≈₁ : Rel ⊸ ℓ₁) (≈₂ : Rel ⊸ ℓ₂) (≈₃ : Rel ⊸ ℓ₃)
    → Set _
  -- _+_ Preserves₂ P ⟶ Q ⟶ R =
  _⊸_ / _+_ Preserves₂ P ⟶ Q ⟶ R = ∀ {a b c} {x y : b ⊸ c} {u v : a ⊸ b} → P x y → Q u v → R (x + u) (y + v)

module M = RelationBinaryMorphismCore

record IsPrecategory {o m ℓ} {O : Set o} (⊸ : B.Rel O m) (∙ : B.TransitiveFlip ⊸) (≈ : M.Rel ⊸ ℓ) : Set (o ⊔ m ⊔ ℓ) where
  field
    isEquivalence : ∀ {x y} → B.IsEquivalence (≈ {x} {y})
    assoc         : M.Associative ⊸ ∙ ≈
    ∙-cong        : ⊸ M./ ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

record Precategory o m ℓ : Set (suc (o ⊔ m ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Object : Set o
    _⊸_ : B.Rel Object m
    _∙_ : B.TransitiveFlip _⊸_
    _≈_ : M.Rel _⊸_ ℓ
    isPrecategory : IsPrecategory _⊸_ _∙_ _≈_

  open IsPrecategory isPrecategory public

module I = Precategory ⦃ … ⦄

instance IsEquivalenceFromPrecategory : ∀ {o m ℓ} ⦃ _ : Precategory o m ℓ ⦄ {x y} → Equality (x I.⊸ y) ℓ
Equality._≋_ IsEquivalenceFromPrecategory = I._≈_
Equality.isEquivalence IsEquivalenceFromPrecategory = I.isEquivalence

module Test where

  postulate
    magic : ∀ {a} {A : Set a} → A
    A : Set
    M : A → A → Set
    _≡M_ : ∀ {x y} → M x y → M x y → Set

  instance PrecategoryM : Precategory _ _ _
  Precategory.Object PrecategoryM = _
  Precategory._⊸_ PrecategoryM = M
  Precategory._∙_ PrecategoryM = magic
  Precategory._≈_ PrecategoryM = _≡M_
  Precategory.isPrecategory PrecategoryM = magic

  open Precategory ⦃ … ⦄

  test-assoc : M.Associative M _∙_ _≋_
  test-assoc = assoc
