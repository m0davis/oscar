
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
open import Oscar.Data.Unifies
import Oscar.Class.Properthing.Ṗroperty
import Oscar.Data.ExtensionṖroperty
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty
import Oscar.Class.Surjection
import Oscar.Property.Propergroup.Substitunction
import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Property.Functor.SubstitunctionExtensionTerm
--import Oscar.Property.Setoid.Proposequality

module Test.ṖropertyFactsSubstitunction {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  open Term 𝔓 using () renaming (
    Term to 𝑩;
    Terms to 𝑩';
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  infix 18 _∼⁰_ _∼¹_
  _∼⁰_ = Unifies₀⟦ 𝑪 ⟧ Proposequality⟦ 𝑩 _ ⟧ -- FIXME "SymUnifies₀⟦ 𝑪 ⟧ Proposequality⟦ 𝑩 _ ⟧" gave us a more useful error message -- FIXME "_∼⁰_ = ≡-Unifies₀⟦ 𝑪 ⟧" had fewer parameters
  _∼¹_ = ≡-ExtensionalUnifies {𝔄 = Fin}

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ c p = surjectextensivity c p

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs c p = surjectextensivity c p

  -- open import Oscar.Property.Setoid.Proposequality
  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉
  -- fact1⋆ 𝓈 𝓉 = symmetrical ⦃ r = 𝓢ymmetricalUnifies₀ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ 𝓢ymmetryProposequality ⦄ ⦄ 𝓈 𝓉

  fact1⋆s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼¹ 𝓉 ≈ 𝓉 ∼¹ 𝓈
  fact1 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 ∼¹ 𝓉 ≈ 𝓉 ∼¹ 𝓈
  fact1s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  Properties-fact1'⋆ : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼⁰ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼⁰ 𝓉₁ ∧ 𝓈₂ ∼⁰ 𝓉₂
  Properties-fact1'⋆ 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = properfact1 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂

  Properties-fact1' : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼¹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼¹ 𝓉₁ ∧ 𝓈₂ ∼¹ 𝓉₂
  Properties-fact1' 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = properfact1 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂

  fact3⋆ : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆ = factsurj3

  fact3 : ∀ {𝓃} {𝒫 : 𝑷¹ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3 = factsurj3

  fact4⋆ : ∀ {𝓂 𝓃} {𝒫 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4⋆ 𝒻 N𝒫 = factsurj4 𝒻 N𝒫

  fact4 : ∀ {𝓂 𝓃} {𝒫 : 𝑷¹ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4 𝒻 N𝒫 = factsurj4 𝒻 N𝒫

  fact5⋆ : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆ 𝒻 𝒫≈𝒬 = surjectextenscongruity 𝒻 𝒫≈𝒬

  fact5 : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5 𝒻 𝒫≈𝒬 = surjectextenscongruity 𝒻 𝒫≈𝒬

  fact6 : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6 𝒫 𝒻≈ℊ = factsurj6 𝒫 𝒻≈ℊ

  left-identity-∧ : ∀ {𝓃} (𝒫 : 𝑷⁰ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧ 𝒫 = ∧-leftIdentity 𝒫

  left-identity-∧-ext : ∀ {𝓃} (𝒫 : 𝑷¹ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧-ext 𝒫 = ∧-leftIdentity 𝒫
