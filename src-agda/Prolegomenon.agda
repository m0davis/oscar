
module Prolegomenon where

open import Agda.Primitive
open import Relation.Binary
open import Algebra
open import Category.Applicative.Predicate

open import Algebra
open import Algebra.Structures
open import Category.Monad.Indexed
open import Algebra.FunctionProperties.Core
open import Function

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
    ◃-≈ᵐ-to-≈ˢ : ≈ᵐ ⇒ ≈ˢ over ◃
    ◃-≈ˢ-to-≈ᵐ : ≈ˢ over ◃ ⇒ ≈ᵐ
    ◃-extracts-∙ : PowerAssociative ≈ˢ ◃ ∙

record MonoidTransformer ℓˢ ℓ⁼ˢ ℓᵐ ℓ⁼ᵐ
  : Set (lsuc (ℓˢ ⊔ ℓ⁼ˢ ⊔ ℓᵐ ⊔ ℓ⁼ᵐ)) where
  field
    base : Setoid ℓˢ ℓ⁼ˢ
    exponent : Monoid ℓᵐ ℓ⁼ᵐ

  open Setoid base public renaming
    (Carrier to Carrierˢ
    ;_≈_ to _≈ˢ_
    ;reflexive to reflexiveˢ
    ;refl to reflˢ
    ;trans to transˢ
    ;sym to symˢ
    )

  open Monoid exponent public renaming
    (Carrier to Carrierᵐ
    ;_≈_ to _≈ᵐ_
    ;reflexive to reflexiveᵐ
    ;_∙_ to _∙_
    ;ε to ε
    ;refl to reflᵐ
    ;trans to transᵐ
    ;sym to symᵐ)

  infixl 6 _◃_
  field
    _◃_ : Carrierᵐ → Carrierˢ → Carrierˢ
    isMonoidTransformer : IsMonoidTransformer _≈ˢ_ _≈ᵐ_ _∙_ ε _◃_

  open IsMonoidTransformer isMonoidTransformer public
