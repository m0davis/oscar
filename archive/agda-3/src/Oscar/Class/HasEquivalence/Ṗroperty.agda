
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.HasEquivalence
open import Oscar.Data.ṖropertyEquivalence
import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Data.Constraint

module Oscar.Class.HasEquivalence.Ṗroperty where

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .⋆ P Q = ṖropertyEquivalence P Q
