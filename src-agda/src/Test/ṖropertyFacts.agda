
open import Oscar.Prelude
open import Oscar.Class.Factsurj3
open import Oscar.Class.Factsurj4
open import Oscar.Class.Factsurj6
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Properfact1
open import Oscar.Class.Properthing
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjectextenscongruity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Symmetrical
open import Oscar.Class.Transitivity
open import Oscar.Data.Surjcollation
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Properthing.Ṗroperty
import Oscar.Class.Surjectextensivity.SurjectivityExtension
import Oscar.Class.Surjectivity.ExtensionArrowExtensionṖropertyProposequality -- needed by 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
import Oscar.Class.Surjectivity.ExtensionLeftṖroperty -- needed by 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
import Oscar.Class.Surjectivity.ExtensionṖroperty -- needed by 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty -- needed by 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
import Oscar.Class.Symmetrical.ExtensionalUnifies
import Oscar.Class.Symmetrical.Unifies
import Oscar.Class.Surjection

-- FIXME remove these dependencies
open import Oscar.Data.Proposequality
import Oscar.Class.[ExtensibleType].Proposequality
import Oscar.Property.Setoid.Proposequality
import Oscar.Property.Setoid.Proposextensequality

module Test.ṖropertyFacts where

  postulate
    𝔞 : Ł
    ¶ : Ø 𝔞

  postulate
    𝔭 : Ł
    𝑩 : ¶ → Ø 𝔭
    𝑩' : ¶ → ¶ → Ø 𝔭
    𝑪₀ : ¶ → Ø ∅̂
    𝑪₁ : ¶ → Ø 𝔭
  𝑪 = Arrow 𝑪₀ 𝑩 -- FIXME why not 𝑪₁? error in 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_; see Oscar.Class.Surjectivity.ExtensionṖroperty
  postulate
    𝒖 : ∀ {n} → 𝑪 n n
    _⊛_ : ∀ {n} → 𝑩 n → 𝑩 n → 𝑩 n

  -- instances from Oscar.Class.HasEquivalence.Substitunction
  instance _ : ∀ {x y} → HasEquivalence (𝑪 x y) _
           _ = ∁ Proposextensequality

  -- *Ṗroperty* stuff
  postulate
    ℓ : Ł
  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_

  module 𝓢 = SurjcollationOperator 𝑪 _≡_
  module 𝓢̇ = SurjextenscollationOperator 𝑪 _≡̇_

  -- postulated instances from Oscar.Property.Functor.SubstitunctionExtensionTerm
  postulate

    instance

      _ : [𝓢urjectivity] 𝑪 (Extension 𝑩)
      _ : 𝓢urjectivity 𝑪 (Extension 𝑩)
      _ : ∀ {N} → [𝓢urjectivity] 𝑪 (Extension $ 𝑩' N)
      _ : ∀ {N} → 𝓢urjectivity 𝑪 (Extension $ 𝑩' N)
      _ : 𝓣ransitivity 𝑪 -- needed by 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
      _ : [𝓢urjextensionality] 𝑪 Proposextensequality (Extension 𝑩) Proposextensequality
      _ : 𝓢urjextensionality 𝑪 Proposextensequality (Extension 𝑩) Proposextensequality -- needed by 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
      _ : ∀ {N} → [𝓢urjextensionality] 𝑪 Proposextensequality (Extension $ 𝑩' N) Proposextensequality
      _ : ∀ {N} → 𝓢urjextensionality 𝑪 Proposextensequality (Extension $ 𝑩' N) Proposextensequality -- needed by 𝓢̇.⟹

  instance _ : 𝓡eflexivity 𝑪 -- needed by [𝓕actsurj3] 𝑷⁰ 𝑪 𝔭
           _ = ∁ 𝒖

  -- postulated instances from Oscar.Property.Propergroup.Substitunction
  postulate

    instance

      _ : [𝓢urjectextenscongruity] 𝑪 𝑷⁰ _≈_
      _ : 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
      _ : [𝓢urjectextenscongruity] 𝑪 𝑷¹ _≈_
      _ : 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_

      _ : ∀ {n} → [𝓟roperfact1] 𝓢._⟹_ (_⊛_ {n = n})
      _ : ∀ {n} → [𝓟roperfact1] 𝓢̇._⟹_ (_⊛_ {n = n})
      _ : ∀ {n} → 𝓟roperfact1 𝓢._⟹_ (_⊛_ {n = n})
      _ : ∀ {n} → 𝓟roperfact1 𝓢̇._⟹_ (_⊛_ {n = n})

      _ : [𝓕actsurj3] 𝑷⁰ 𝑪 𝔭
      _ : 𝓕actsurj3 𝑷⁰ 𝑪
      _ : [𝓕actsurj3] 𝑷¹ 𝑪 𝔭
      _ : 𝓕actsurj3 𝑷¹ 𝑪

  instance _ : [𝓕actsurj4] 𝑷⁰ 𝑪 Nothing
           _ = ∁ surjectextensivity
  postulate instance _ : 𝓕actsurj4 𝑷⁰ 𝑪 Nothing
  instance _ : [𝓕actsurj4] 𝑷¹ 𝑪 Nothing
           _ = ∁ surjectextensivity
  postulate instance _ : 𝓕actsurj4 𝑷¹ 𝑪 Nothing

  postulate
    instance
      _ : [𝓕actsurj6] 𝑷¹ 𝑪 _≈_ _≈_
      _ : 𝓕actsurj6 𝑷¹ 𝑪 _≈_ _≈_

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
