
open import Oscar.Prelude

module Oscar.Class.Symmetrical where

record 𝓢ymmetrical
  {𝔞} (𝔄 : Ø 𝔞)
  {ℓ} (_∼_↦_∼_ : 𝔄 → 𝔄 → 𝔄 → 𝔄 → Ø ℓ)
  : Ø 𝔞 ∙̂ ℓ where
  field
    symmetrical : (x y : 𝔄) → x ∼ y ↦ y ∼ x

open 𝓢ymmetrical ⦃ … ⦄ public
