
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Symmetrical
open import Oscar.Data
open import Oscar.Data.Unifies
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.Symmetrical.ExtensionalUnifies
import Oscar.Class.Symmetrical.Unifies
import Oscar.Property.Setoid.Proposequality -- FIXME see fact1⋆ below; comment this out to observe confusing error messages
import Oscar.Property.Functor.SubstitunctionExtensionTerm

module Test.Surjcollation {𝔭} (𝔓 : Ø 𝔭) where
  open Term 𝔓
  open Substitunction 𝔓

  module 𝓢 = Surjcollation Substitunction (λ ℓ _ → Lift (ℓ ≡ ∅̂)) (λ {⦃ lift ∅ ⦄ → ∁ Proposequality} )
  module 𝓢̇ = Surjextenscollation Substitunction Proposequality

  fact1⋆ : ∀ {𝓃} (𝓈 𝓉 : Term 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆ 𝓈 𝓉 = symmetrical 𝓈 𝓉
  -- fact1⋆ 𝓈 𝓉 = symmetrical ⦃ r = Oscar.Class.Symmetrical.Unifies.𝓢ymmetricalUnifies₀ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ Oscar.Property.Setoid.Proposequality.𝓢ymmetryProposequality ⦄ ⦄ 𝓈 𝓉 -- FIXME I wish Agda would tell us that this is how the instances were resolved

  fact1⋆s : ∀ {N 𝓃} (𝓈 𝓉 : Terms N 𝓃) → 𝓈 𝓢.⟹ 𝓉 ≈ 𝓉 𝓢.⟹ 𝓈
  fact1⋆s 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1 : ∀ {𝓃} (𝓈 𝓉 : Term 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1 𝓈 𝓉 = symmetrical 𝓈 𝓉

  fact1s : ∀ {N 𝓃} (𝓈 𝓉 : Terms N 𝓃) → 𝓈 𝓢̇.⟹ 𝓉 ≈ 𝓉 𝓢̇.⟹ 𝓈
  fact1s 𝓈 𝓉 = symmetrical 𝓈 𝓉
