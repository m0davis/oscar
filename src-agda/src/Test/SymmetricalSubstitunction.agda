
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Symmetrical
open import Oscar.Data
open import Oscar.Data.Unifies
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.Symmetrical.ExtensionalUnifies
import Oscar.Class.Symmetrical.Unifies
import Oscar.Data.ExtensionṖroperty
import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Property.Setoid.Proposequality -- FIXME (comment this out to observe confusing error messages)
import Oscar.Property.Functor.SubstitunctionExtensionTerm

module Test.SymmetricalSubstitunction {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
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
  _∼⁰_ = ≡-SymUnifies₀⟦ 𝑪 ⟧ -- FIXME "Unifies₀⟦ 𝑪 ⟧ Proposequality⟦ 𝑩 _ ⟧" gives a confusing error message -- FIXME "SymUnifies₀⟦ 𝑪 ⟧ Proposequality⟦ 𝑩 _ ⟧" gave us a more useful error message -- FIXME "_∼⁰_ = ≡-Unifies₀⟦ 𝑪 ⟧" had fewer parameters
  _∼¹_ = ≡-ExtensionalUnifies

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉
  -- fact1⋆ 𝓈 𝓉 = symmetrical ⦃ r = 𝓢ymmetricalUnifies₀ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ 𝓢ymmetryProposequality ⦄ ⦄ 𝓈 𝓉

  fact1⋆s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 ∼⁰ 𝓉 ≈ 𝓉 ∼⁰ 𝓈
  fact1⋆s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1 : ∀ {𝓃} (𝓈 𝓉 : 𝑩 𝓃) → 𝓈 ∼¹ 𝓉 ≈ 𝓉 ∼¹ 𝓈
  fact1 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1s : ∀ {N 𝓃} (𝓈 𝓉 : 𝑩' N 𝓃) → 𝓈 ∼¹ 𝓉 ≈ 𝓉 ∼¹ 𝓈
  fact1s 𝓈 𝓉 = symmetrical 𝓈 𝓉
