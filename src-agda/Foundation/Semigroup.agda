
module Foundation.Semigroup where

open import Foundation.Primitive
open import Foundation.Equivalence
open import Agda.Primitive

record IsAssociative {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ (_∙_ : A → A → A) : ℞ a ⊔ ℓ where
  field
    associativity : ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

open IsAssociative ⦃ … ⦄

record Semigroup {c} (A : Set c) ℓ : Set (c ⊔ ⟰ ℓ) where
  field
    ⦃ equivalence ⦄ : Equivalence A ℓ
    _∙_ : A → A → A
    isAssociative : IsAssociative _∙_

open Semigroup ⦃ … ⦄

record Monoid {a} (A : Set a) ℓ : Set (a ⊔ ⟰ ℓ) where
  field
    ⦃ semigroup ⦄ : Semigroup A ℓ
    ε : A
    left-identity : ∀ x → ε ∙ x ≈ x
    right-identity : ∀ x → x ∙ ε ≈ x

open Monoid ⦃ … ⦄

open import Relation.Binary.Core
open import Algebra.FunctionProperties.Core

PowerRightIdentity : ∀ {a ℓ} {A : Set a} → Rel A ℓ → ∀ {b} {B : Set b} → B → (B → A → A) → Set _
PowerRightIdentity _≈_ e _◃_ = ∀ x → (e ◃ x) ≈ x

PowerAssociative : ∀ {a b ℓ} {A : Set a} {B : Set b} → (A → A → Set ℓ) → (B → A → A) → (B → B → B) → Set _
PowerAssociative _≈_ _◃_ _∙_ = ∀ x a b → ((b ∙ a) ◃ x) ≈ (b ◃ (a ◃ x))

_over_ : ∀ {f} {F : Set f} {g} → (F → F → Set g) → ∀ {i} {I : Set i} {a} {A : Set a} → (A → I → F) → A → A → Set (i ⊔ g)
_*_ over f = λ x y → ∀ i → f x i * f y i

record IsMonoidTransformer {s ℓˢ} {S : Set s} (≈ˢ : Rel S ℓˢ) {m ℓᵐ} {M : Set m} (≈ᵐ : Rel M ℓᵐ) (∙ : Op₂ M) (ε : M) (◃ : M → S → S) : Set (s ⊔ ℓˢ ⊔ m ⊔ ℓᵐ) where
  field
    ◃-identity : PowerRightIdentity ≈ˢ ε ◃
    ≈ˢ-over-◃-⟶-≈ᵐ : ≈ˢ over ◃ ⇒ ≈ᵐ
    ≈ᵐ-to-≈ˢ-over-◃ : ≈ᵐ ⇒ ≈ˢ over ◃
    ◃-extracts-∙ : PowerAssociative ≈ˢ ◃ ∙

open IsMonoidTransformer ⦃ … ⦄

record MonoidTransformer {s} (S : Set s) ℓˢ {m} (M : Set m) ℓᵐ : Set (s ⊔ m ⊔ lsuc (ℓˢ ⊔ ℓᵐ)) where
  field
    ⦃ base ⦄ : Equivalence S ℓˢ
    ⦃ exponent ⦄ : Monoid M ℓᵐ

  infixl 6 _◃_
  field
    _◃_ : M → S → S
    instance isMonoidTransformer : IsMonoidTransformer _≈_ _≈_ _∙_ ε _◃_
