
open import Oscar.Prelude
open import Oscar.Class

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
  open ℭlass (𝔩eftunit _↦_ ε _◃_) using () renaming (GET-CLASS to Leftunit; GET-METHOD to leftunit⟦_/_/_⟧) public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  open ℭlass (𝔩eftunit _↦_ ε _◃_) using () renaming (GET-METHOD to leftunit) public
