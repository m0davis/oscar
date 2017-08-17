
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.Leftunit where

module $Family
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  =
    ℭLASS (ε , _◃_ , _↦_) (ε ◃ x ↦ x)
    -- Unit (ε ◃ x ↦ x)

module $MethodSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  {x : 𝔄}
  where
  method = $Family.method _↦_ ε _◃_ x

module $FamilyInstance
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ} (let _↦_ = _↦_; infix 4 _↦_)
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄} (let _◃_ = _◃_; infix 16 _◃_)
  {x : 𝔄}
  ⦃ _ : $Family.class _↦_ ε _◃_ x ⦄
  where
  instance
    I : Unit.class (ε ◃ x ↦ x)
    I .⋆ = $MethodSingle.method

module LeftunitsV
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  class = ∀ {x} → $Family.class _↦_ ε _◃_ x
  type = ∀ x → $Family.type _↦_ ε _◃_ x
  method = λ ⦃ _ : class ⦄ x → $Family.method _↦_ ε _◃_ x

module leftunitsV
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  method = LeftunitsV.method _↦_ ε _◃_

module LeftunitsH
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  class = ∀ {x} → $Family.class _↦_ ε _◃_ x
  type = ∀ {x} → $Family.type _↦_ ε _◃_ x
  method = λ ⦃ _ : class ⦄ {x} → $Family.method _↦_ ε _◃_ x

module leftunitsH
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  method = LeftunitsH.method _↦_ ε _◃_
