
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit
open import Oscar.Class.Leftunit

module Oscar.Class.Leftunit.ToUnit where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ} (let _↦_ = _↦_; infix 4 _↦_)
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄} (let _◃_ = _◃_; infix 16 _◃_)
  {x : 𝔄}
  ⦃ _ : Leftunit.class _↦_ ε _◃_ x ⦄
  where
  instance
    Leftunit--Unit : Unit.class (ε ◃ x ↦ x)
    Leftunit--Unit .⋆ = leftunit
