
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
open import Oscar.Data.Surjcollation
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

-- FIXME remove these dependencies
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
import Oscar.Class.[ExtensibleType].Proposequality
import Oscar.Property.Setoid.Proposequality
import Oscar.Property.Functor.SubstitunctionExtensionTerm

module Test.ṖropertyFacts {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  open Term 𝔓 using () renaming (
    Term to 𝑩;
    Terms to 𝑩';
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  module 𝓢 = SurjcollationOperator 𝑪 _≡_
  module 𝓢̇ = SurjextenscollationOperator 𝑪 _≡̇_

  postulate
    instance _ : [𝓢urjectextenscongruity] 𝑪 𝑷⁰ _≈_
    instance _ : 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
    instance _ : [𝓢urjectextenscongruity] 𝑪 𝑷¹ _≈_
    instance _ : 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
    instance _ : ∀ {n} → [𝓟roperfact1] 𝓢._⟹_ (_⊛_ {n = n})
    instance _ : ∀ {n} → [𝓟roperfact1] 𝓢̇._⟹_ (_⊛_ {n = n})
    instance _ : ∀ {n} → 𝓟roperfact1 𝓢._⟹_ (_⊛_ {n = n})
    instance _ : ∀ {n} → 𝓟roperfact1 𝓢̇._⟹_ (_⊛_ {n = n})
    instance _ : [𝓕actsurj3] 𝑷⁰ 𝑪 𝔭
    instance _ : 𝓕actsurj3 𝑷⁰ 𝑪
    instance _ : [𝓕actsurj3] 𝑷¹ 𝑪 𝔭
    instance _ : 𝓕actsurj3 𝑷¹ 𝑪

  instance _ : [𝓕actsurj4] 𝑷⁰ 𝑪 Nothing
           _ = ∁ surjectextensivity
  postulate
    instance _ : 𝓕actsurj4 𝑷⁰ 𝑪 Nothing
  instance _ : [𝓕actsurj4] 𝑷¹ 𝑪 Nothing
           _ = ∁ surjectextensivity
  postulate
    instance _ : 𝓕actsurj4 𝑷¹ 𝑪 Nothing
    instance _ : [𝓕actsurj6] 𝑷¹ 𝑪 _≈_ _≈_
    instance _ : 𝓕actsurj6 𝑷¹ 𝑪 _≈_ _≈_

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ c p = surjectextensivity c p

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs c p = surjectextensivity c p

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1⋆s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  Properties-fact1'⋆ : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ 𝓢.⟹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ 𝓢.⟹ 𝓉₁ ∧ 𝓈₂ 𝓢.⟹ 𝓉₂
  Properties-fact1'⋆ 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = properfact1 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂

  Properties-fact1' : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ 𝓢̇.⟹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ 𝓢̇.⟹ 𝓉₁ ∧ 𝓈₂ 𝓢̇.⟹ 𝓉₂
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
