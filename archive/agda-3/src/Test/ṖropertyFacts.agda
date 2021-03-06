
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Properthing.Ṗroperty
import Oscar.Class.Surjection.⋆
import Oscar.Class.Smap.ExtensionṖroperty -- needed by 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
import Oscar.Class.Smap.TransitiveExtensionLeftṖroperty -- needed by 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
import Oscar.Class.Symmetrical.ExtensionalUnifies
import Oscar.Class.Symmetrical.Unifies
open import Oscar.Class
open import Oscar.Class.HasEquivalence
open import Oscar.Class.IsEquivalence
open import Oscar.Class.Leftstar
open import Oscar.Class.Leftunit
open import Oscar.Class.Properthing
open import Oscar.Class.Quadricity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Similarity
open import Oscar.Class.SimilaritySingleton
open import Oscar.Class.SimilarityM
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Symmetrical
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.Unit
open import Oscar.Class.[ExtensibleType]
open import Oscar.Data.Surjcollation
open import Oscar.Data.Surjextenscollation
open import Oscar.Prelude
import Oscar.Class.Leftunit.ToUnit

import Everything -- FIXME doesn't work with open

module Test.ṖropertyFacts where

  postulate
    Proposequality : ∀ {𝔬} {𝔒 : Ø 𝔬} (𝓞 : 𝔒) → 𝔒 → Ø₀

  infix 4 _≡_
  _≡_ = Proposequality

  Proposequality⟦_⟧ : ∀ {𝔬} (𝔒 : Ø 𝔬) → 𝔒 → 𝔒 → Ø₀
  Proposequality⟦ _ ⟧ = Proposequality

  Proposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality 𝓟₁ 𝓟₂ = ∀ 𝓞 → Proposequality (𝓟₁ 𝓞) (𝓟₂ 𝓞)

  infix 4 _≡̇_
  _≡̇_ = Proposextensequality

  Proposextensequality⟦_⟧ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality⟦ _ ⟧ = Proposextensequality

  postulate
    𝔞 : Ł
    ¶ : Ø 𝔞

  postulate
    𝔭 : Ł
    𝑩 : ¶ → Ø 𝔭
    𝑩' : ¶ → ¶ → Ø 𝔭
    𝑪₀ : ¶ → Ø ∅̂
    𝑪₁ : ¶ → Ø 𝔭
  𝑪 = Arrow 𝑪₀ 𝑩 -- FIXME why not 𝑪₁? error in 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_; see Oscar.Class.Smap.ExtensionṖroperty
  postulate
    𝒖 : ∀ {n} → 𝑪 n n
    _⊛_ : ∀ {n} → 𝑩 n → 𝑩 n → 𝑩 n

  -- postulated instances from Oscar.Property.Setoid.Proposextensequality
  postulate
    instance _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → IsEquivalence Proposextensequality⟦ 𝔓 ⟧

  -- instances from Oscar.Class.HasEquivalence.Substitunction
  instance _ : ∀ {x y} → HasEquivalence (𝑪 x y) _
           _ = ∁ Proposextensequality

  -- *Ṗroperty* stuff
  postulate
    ℓ : Ł
  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_

  module 𝓢 = Surjcollation 𝑪 _≡_
  module 𝓢̇ = Surjextenscollation 𝑪 _≡̇_

  -- postulated instances from Oscar.Property.Functor.SubstitunctionExtensionTerm
  postulate

    instance

      _ : Smap!.class 𝑪 (Extension 𝑩)
      _ : ∀ {N} → Smap!.class 𝑪 (Extension $ 𝑩' N)
      _ : Transitivity.class 𝑪 -- needed by 𝓢urjectextenscongruity 𝑪 𝑷⁰ _≈_
      _ : Surjextensionality!.class 𝑪 Proposextensequality (Extension 𝑩) Proposextensequality -- needed by 𝓢urjectextenscongruity 𝑪 𝑷¹ _≈_
      _ : ∀ {N} → Surjextensionality!.class 𝑪 Proposextensequality (Extension $ 𝑩' N) Proposextensequality -- needed by 𝓢̇.⟹

  instance _ : Reflexivity.class 𝑪 -- needed by [𝓕actsurj3] 𝑷⁰ 𝑪 𝔭
           _ = ∁ 𝒖

  -- postulated instances from Oscar.Property.Setoid.Proposequality
  postulate
    instance _ : ∀ {𝔬} {𝔒 : Ø 𝔬} → Symmetry.class Proposequality⟦ 𝔒 ⟧
    instance _ : ∀ {𝔬} {𝔒 : Ø 𝔬} → Transitivity.class Proposequality⟦ 𝔒 ⟧

  -- postulated instances from Oscar.Class.[ExtensibleType].Proposequality
  postulate
    instance _ : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)

  -- postulated instances from Oscar.Property.Propergroup.Substitunction
  postulate

    instance

      _ : Similarity,smaphomarrow!.class 𝑪 𝑷⁰ _≈_
      _ : Similarity,smaphomarrow!.class 𝑪 𝑷¹ _≈_

      _ : ∀ {n} → Properfact1.class 𝓢._⟹_ (_⊛_ {n = n})
      _ : ∀ {n} → Properfact1.class 𝓢̇._⟹_ (_⊛_ {n = n})

      _ : Leftunit,equivalence,smaphomarrow!.class 𝑪 𝑷⁰
      _ : Leftunit,equivalence,smaphomarrow!.class 𝑪 𝑷¹

      _ : Leftstar,smaphomarrow!.class 𝑷⁰ 𝑪 Nothing
      _ : Leftstar,smaphomarrow!.class 𝑷¹ 𝑪 Nothing

  postulate
    instance
      _ : Similarity,cosmaphomarrow!.class 𝑪 𝑷¹ _≈_ _≈_

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ c p = smaparrow c p

  test-epfs⋆' : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆' c p = smap c $ p

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs c p = smaparrow c p

  test-epfs' : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs' c p = smap c $ p

  fact5⋆ : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆ 𝒻 = ‼

  fact5⋆' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆' 𝒻 𝒫≈𝒬 = similaritySingleton 𝒫≈𝒬

  fact5⋆'' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆'' 𝒻 𝒫≈𝒬 = similarity 𝒻 𝒫≈𝒬

  fact5⋆''' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆''' 𝒻 𝒫≈𝒬 = similarityM 𝒻 𝒫≈𝒬

  fact5⋆'''' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5⋆'''' = ‼

  fact5 : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5 𝒻 = ‼

  fact5' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5' 𝒻 𝒫≈𝒬 = similaritySingleton 𝒫≈𝒬

  fact5'' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5'' 𝒻 𝒫≈𝒬 = similarity 𝒻 𝒫≈𝒬

  fact5''' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5''' 𝒻 𝒫≈𝒬 = similarityM 𝒻 𝒫≈𝒬

  fact5'''' : ∀ {𝓂 𝓃} {𝒫 𝒬 : 𝑷¹ 𝓂} (𝒻 : 𝑪 𝓂 𝓃) → 𝒫 ≈ 𝒬 → 𝒻 ◃ 𝒫 ≈ 𝒻 ◃ 𝒬
  fact5'''' = ‼

  fact6 : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6 𝒫 𝒻≈ℊ = similarity 𝒫 𝒻≈ℊ

  fact6' : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6' 𝒫 𝒻≈ℊ = similarityM 𝒫 𝒻≈ℊ

  fact6'' : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6'' = ‼

  fact3⋆ : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆ = ‼

  fact3⋆-Leftunit : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆-Leftunit {𝒫 = 𝒫} = Leftunit.method (flip _≈_) 𝒖 smaparrow 𝒫

  fact3⋆-leftunit : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆-leftunit = leftunit

  lhs-fact3⋆ : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → _
  lhs-fact3⋆ {𝒫 = 𝒫} = Leftunit,equivalence,smaphomarrow!.method 𝑪 𝑷⁰ {p = 𝒫}

  fact3 : ∀ {𝓃} {𝒫 : 𝑷¹ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3 = ‼

  fact4⋆ : ∀ {𝓂 𝓃} {𝒫 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4⋆ 𝒻 N𝒫 = leftstar 𝒻 N𝒫

  fact4 : ∀ {𝓂 𝓃} {𝒫 : 𝑷¹ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4 𝒻 N𝒫 = leftstar 𝒻 N𝒫

  left-identity-∧ : ∀ {𝓃} (𝒫 : 𝑷⁰ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧ 𝒫 = ∧-leftIdentity 𝒫

  left-identity-∧-ext : ∀ {𝓃} (𝒫 : 𝑷¹ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧-ext 𝒫 = ∧-leftIdentity 𝒫

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1⋆s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1 𝓈 𝓉 = symmetrical 𝓈 𝓉

  lhs-fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → _
  lhs-fact1 𝓈 𝓉 = symmetrical⟦ 𝓢̇._⟹_ / _≈_ ⟧ 𝓈 𝓉

  fact1s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  Properties-fact1'⋆ : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ 𝓢.⟹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ 𝓢.⟹ 𝓉₁ ∧ 𝓈₂ 𝓢.⟹ 𝓉₂
  Properties-fact1'⋆ 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = quadricity 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂

  Properties-fact1' : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ 𝓢̇.⟹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ 𝓢̇.⟹ 𝓉₁ ∧ 𝓈₂ 𝓢̇.⟹ 𝓉₂
  Properties-fact1' 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = quadricity 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂
