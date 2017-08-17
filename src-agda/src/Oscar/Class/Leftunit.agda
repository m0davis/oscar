
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
  where
  --module class = ℭLASS (ε , _◃_ , _↦_) (ε ◃ x ↦ x)
  module class = Unit (ε ◃ x ↦ x)

module $ClassSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  (x : 𝔄)
  where
  class = $Family.class.class _↦_ ε _◃_ x
  type = $Family.class.type _↦_ ε _◃_ x
  method = $Family.class.method _↦_ ε _◃_ x

module $MethodSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  {x : 𝔄}
  where
  method = $ClassSingle.method _↦_ ε _◃_ x

module $ClassAll
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  class = ∀ {x} → $ClassSingle.class _↦_ ε _◃_ x
  type = ∀ x → $ClassSingle.type _↦_ ε _◃_ x
  method = λ ⦃ _ : class ⦄ x → $ClassSingle.method _↦_ ε _◃_ x

module $MethodAll
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  method = $ClassAll.method _↦_ ε _◃_

module $ClassAllH
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  class = ∀ {x} → $ClassSingle.class _↦_ ε _◃_ x
  type = ∀ {x} → $ClassSingle.type _↦_ ε _◃_ x
  method = λ ⦃ _ : class ⦄ {x} → $ClassSingle.method _↦_ ε _◃_ x

module $MethodAllH
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  method = $ClassAllH.method _↦_ ε _◃_

module Leftunit = $ClassAll
module leftunit = $MethodAllH
