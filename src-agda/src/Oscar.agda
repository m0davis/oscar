-- the latest developments are tested here

module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
open import Test

module ṖropertyFactsSubstitunction {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  open Term 𝔓 using () renaming (
    Term to Term;
    i to i;
    _fork_ to _fork_)
  open Substitunction 𝔓 using () renaming (
    Substitunction to 𝑨)

  𝑷⁰ = LeftṖroperty ℓ 𝑨
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑨 _≈_
  infix 18 _∼⁰_ _∼¹_
  _∼⁰_ = ≡-Unifies₀⟦ 𝑨 ⟧
  _∼¹_ = ≡-ExtensionalUnifies {𝔄 = Fin}

  test-epfs⋆ : ∀ {x y} → 𝑨 x y → 𝑷⁰ x → 𝑷⁰ y
  test-epfs⋆ = surjectextensivity

  test-epfs : ∀ {x y} → 𝑨 x y → 𝑷¹ x → 𝑷¹ y
  test-epfs = surjectextensivity

  fact1⋆ : ∀ {m} (s t : Term m) → s ∼⁰ t ≈ t ∼⁰ s
  fact1⋆ = symmetrical

  fact1 : ∀ {m} (s t : Term m) → s ∼¹ t ≈ t ∼¹ s
  fact1 = symmetrical

  Properties-fact1'⋆ : ∀ {n} (s₁ s₂ t₁ t₂ : Term n) → s₁ fork s₂ ∼⁰ t₁ fork t₂ ≈ s₁ ∼⁰ t₁ ∧ s₂ ∼⁰ t₂
  Properties-fact1'⋆ = properfact1

  Properties-fact1' : ∀ {n} (s₁ s₂ t₁ t₂ : Term n) → s₁ fork s₂ ∼¹ t₁ fork t₂ ≈ s₁ ∼¹ t₁ ∧ s₂ ∼¹ t₂
  Properties-fact1' = properfact1

  fact3⋆ : ∀ {m} {P : 𝑷⁰ m} → P ≈ i ◃ P
  fact3⋆ = factsurj3

  fact3 : ∀ {m} {P : 𝑷¹ m} → P ≈ i ◃ P
  fact3 = factsurj3

  fact4⋆ : ∀ {m n} (P : 𝑷⁰ m) (f : 𝑨 _ n) → Nothing P → Nothing (f ◃ P)
  fact4⋆ = factsurj4

  fact4 : ∀ {m n} (P : 𝑷¹ m) (f : 𝑨 _ n) → Nothing P → Nothing (f ◃ P)
  fact4 = factsurj4

  fact5⋆ : ∀ {m n} {P Q : 𝑷⁰ m} (f : 𝑨 m n) → P ≈ Q → f ◃ P ≈ f ◃ Q
  fact5⋆ = surjectextenscongruity

  fact5 : ∀ {m n} {P Q : 𝑷¹ m} (f : 𝑨 m n) → P ≈ Q → f ◃ P ≈ f ◃ Q
  fact5 = surjectextenscongruity

  fact6 : ∀ {m n} (P : 𝑷¹ m) {f g : 𝑨 m n} → f ≈ g → f ◃ P ≈ g ◃ P
  fact6 = factsurj6

  left-identity-∧ : ∀ {m} (P : 𝑷⁰ m) → ➊ ∧ P ≈ P
  left-identity-∧ = ∧-leftIdentity

  left-identity-∧-ext : ∀ {m} (P : 𝑷¹ m) → ➊ ∧ P ≈ P
  left-identity-∧-ext = ∧-leftIdentity
