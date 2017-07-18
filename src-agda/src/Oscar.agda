-- the latest developments are tested here

module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
open import Test

module ṖropertyFactsSubstitunction {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  open Term 𝔓 using () renaming (
    Term to 𝑩;
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  infix 18 _∼⁰_ _∼¹_
  _∼⁰_ = ≡-Unifies₀⟦ 𝑪 ⟧
  _∼¹_ = ≡-ExtensionalUnifies {𝔄 = Fin}

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ = surjectextensivity

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs = surjectextensivity

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆ = symmetrical

  fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼¹ 𝓉 ≈ 𝓉 ∼¹ 𝓈
  fact1 = symmetrical

  Properties-fact1'⋆ : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼⁰ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼⁰ 𝓉₁ ∧ 𝓈₂ ∼⁰ 𝓉₂
  Properties-fact1'⋆ = properfact1

  Properties-fact1' : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼¹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼¹ 𝓉₁ ∧ 𝓈₂ ∼¹ 𝓉₂
  Properties-fact1' = properfact1

  fact3⋆ : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆ = factsurj3

  fact3 : ∀ {𝓃} {𝒫 : 𝑷¹ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3 = factsurj3

  fact4⋆ : ∀ {𝓂 𝓃} (𝒫 : 𝑷⁰ 𝓂) (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4⋆ = factsurj4

  fact4 : ∀ {𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4 = factsurj4

  fact5⋆ : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆ = surjectextenscongruity

  fact5 : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5 = surjectextenscongruity

  fact6 : ∀ {𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) {𝒻 g : 𝑪 𝓂 𝓃} → 𝒻 ≈ g → 𝒻 ◃ 𝒫 ≈ g ◃ 𝒫
  fact6 = factsurj6

  left-identity-∧ : ∀ {𝓃} (𝒫 : 𝑷⁰ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧ = ∧-leftIdentity

  left-identity-∧-ext : ∀ {𝓃} (𝒫 : 𝑷¹ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧-ext = ∧-leftIdentity
