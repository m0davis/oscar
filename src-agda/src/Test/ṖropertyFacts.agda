
open import Oscar.Prelude
open import Oscar.Class.Factsurj3
open import Oscar.Class.Factsurj4
open import Oscar.Class.Factsurj6
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Properfact1
open import Oscar.Class.Properthing
open import Oscar.Class.Surjectextenscongruity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Symmetrical
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Surjcollation
open import Oscar.Data.Term
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.HasEquivalence.Substitunction
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Properthing.Ṗroperty
import Oscar.Class.Surjectextensivity.SurjectivityExtension
import Oscar.Class.Surjectivity.ExtensionArrowExtensionṖropertyProposequality
import Oscar.Class.Surjectivity.ExtensionLeftṖroperty
import Oscar.Class.Surjectivity.ExtensionṖroperty
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty
import Oscar.Class.Symmetrical.ExtensionalUnifies
import Oscar.Class.Symmetrical.Unifies
import Oscar.Class.[ExtensibleType].Proposequality
import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Property.Propergroup.Substitunction
import Oscar.Property.Setoid.Proposequality

module Test.ṖropertyFacts {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  -- FIXME generalise, removing dependency on Substitunction datatype
  open Term 𝔓 using () renaming (
    Term to 𝑩;
    Terms to 𝑩';
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  infix 18 _∼⁰_
  _∼⁰_ = ≡-surjcollation⟦ 𝑪 ⟧
  open SurjextenscollationOperator 𝑪 _≡̇_ renaming (_⟹_ to _∼¹_)

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ c p = surjectextensivity c p

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs c p = surjectextensivity c p

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉

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
