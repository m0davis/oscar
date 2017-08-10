
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftunit where

module Unit
  {𝔞} (𝔄 : Ø 𝔞)
  where
  𝔲nit : ℭlass $′ 𝔄
  𝔲nit = ∁ 𝔄

module $Family
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  where
  family = ℭlass (ε , _◃_ , _↦_) ∋ (∁ $′ ε ◃ x ↦ x)
  module class = ℭLASS family

module $ClassSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  (x : 𝔄)
  where
  class = $Family.class.𝒄lass _↦_ ε _◃_ x
  type = $Family.class.𝒕ype _↦_ ε _◃_ x
  method = $Family.class.𝒎ethod _↦_ ε _◃_ x

module $ClassAll
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  class = ∀ {x} → $ClassSingle.class _↦_ ε _◃_ x
  type = ∀ x → $ClassSingle.type _↦_ ε _◃_ x
  method = λ ⦃ _ : class ⦄ x → $ClassSingle.method _↦_ ε _◃_ x

module $MethodSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  {x : 𝔄}
  where
  method = $ClassSingle.method _↦_ ε _◃_ x

module $MethodAll
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  method = $ClassAll.method _↦_ ε _◃_

module Leftunit
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  where
  private
    𝔩eftunit : ℭlass (ε , _◃_ , _↦_ , x) -- FIXME including x helps instance search not confuse with the 'all x' case
    𝔩eftunit = ∁ $′ ε ◃ x ↦ x
  open ℭLASS 𝔩eftunit public
  P𝔩eftunit = 𝔩eftunit

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
