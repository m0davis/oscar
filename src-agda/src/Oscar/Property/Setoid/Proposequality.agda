
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.IsEquivalence
open import Oscar.Class.Setoid
open import Oscar.Data.Proposequality

module Oscar.Property.Setoid.Proposequality where

module _ {𝔬} {𝔒 : Ø 𝔬} where

  instance

    𝓡eflexivityProposequality : Reflexivity.class Proposequality⟦ 𝔒 ⟧
    𝓡eflexivityProposequality .⋆ = !

    𝓢ymmetryProposequality : 𝓢ymmetry Proposequality⟦ 𝔒 ⟧
    𝓢ymmetryProposequality {x∼y = ∅} .⋆ = !

    𝓣ransitivityProposequality : Transitivity.class Proposequality⟦ 𝔒 ⟧
    𝓣ransitivityProposequality {x∼y = ∅} {y∼z} .⋆ = y∼z

    IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
    IsEquivalenceProposequality = ∁

module _ {𝔬} (𝔒 : Ø 𝔬) where

  SetoidProposequality : Setoid _ _
  SetoidProposequality = ∁ Proposequality⟦ 𝔒 ⟧
