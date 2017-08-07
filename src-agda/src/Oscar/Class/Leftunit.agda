
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data.Constraint

module Oscar.Class.Leftunit where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  𝔩eftunit : ℭlass (ε , _◃_ , _↦_)
  𝔩eftunit = ∁ ∀ {x} → (ε ◃ x) ↦ x

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  open ℭlass (𝔩eftunit _↦_ ε _◃_)
  Leftunit = GET-CLASS
  leftunit⟦_/_/_⟧ : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftunit⟦_/_/_⟧ = GET-METHOD

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  open ℭlass (𝔩eftunit _↦_ ε _◃_)
  leftunit : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftunit = GET-METHOD
