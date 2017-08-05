
open import Oscar.Prelude
open import Oscar.Class.Properthing
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Quadricity

module Oscar.Class.Properfact1 where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} (_∼_ : 𝔄 → 𝔄 → 𝔅) {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  𝓹roperfact1 = 𝒬uadricity _≈_ _∧_ _∼_ _⊛_
  𝓟roperfact1 = Quadricity _≈_ _∧_ _∼_ _⊛_
