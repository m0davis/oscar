
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftunit where

module Leftunit
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  where
  private
    𝔩eftunit : ℭlass (ε , _◃_ , _↦_)
    𝔩eftunit = ∁ $′ ε ◃ x ↦ x
  open ℭLASS 𝔩eftunit public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  (x : 𝔄)
  where
  leftunit⟦_/_/_⟧ : ⦃ _ : Leftunit.𝒄lass _↦_ ε _◃_ x ⦄ → Leftunit.𝒕ype _↦_ ε _◃_ x
  leftunit⟦_/_/_⟧ = Leftunit.𝒎ethod _↦_ ε _◃_ x

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  {x : 𝔄}
  where
  leftunit = Leftunit.𝒎ethod _↦_ ε _◃_ x
