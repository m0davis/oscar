
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.IsEquivalence
open import Oscar.Class.Setoid
open import Oscar.Data.Proposequality

module Oscar.Property.Setoid.Proposextensequality where

module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

  instance

    𝓡eflexivityProposextensequality : Reflexivity.class Proposextensequality⟦ 𝔓 ⟧
    𝓡eflexivityProposextensequality .⋆ _ = ∅

    𝓢ymmetryProposextensequality : Symmetry.class Proposextensequality⟦ 𝔓 ⟧
    𝓢ymmetryProposextensequality .⋆ f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

    𝓣ransitivityProposextensequality : Transitivity.class Proposextensequality⟦ 𝔓 ⟧
    𝓣ransitivityProposextensequality .⋆ f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

    IsEquivalenceProposextensequality : IsEquivalence Proposextensequality⟦ 𝔓 ⟧
    IsEquivalenceProposextensequality = ∁

module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

  SetoidProposextensequality : Setoid _ _
  SetoidProposextensequality = ∁ Proposextensequality⟦ 𝔓 ⟧
