
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftunit where

module Unit
  {𝔞} (𝔄 : Ø 𝔞)
  where
  𝔲nit : ℭlass $′ 𝔄
  𝔲nit = ∁ 𝔄

module $SimplerFamily
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔈 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (x : 𝔄)
  where
  𝔣amily : ℭlass $′ _↦_ , x , ε
  𝔣amily = ∁ (ε ↦ x)

module $Family
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  where
  -- family = ℭlass (ε , _◃_ , _↦_) ∋ (∁ $′ ε ◃ x ↦ x)
  -- family = ℭlass (ε , _◃_) ∋ (∁ $′ ε ◃ x ↦ x)
  family = Unit.𝔲nit (ε ◃ x ↦ x)
  -- family = $SimplerFamily.𝔣amily (λ ε x → ε ◃ x ↦ x) ε x
  module class = ℭLASS family

module $MethodUnit
  {𝔞} {𝔄 : Ø 𝔞}
  where
  module class = ℭLASS (Unit.𝔲nit 𝔄)
  method = class.𝒎ethod

!! = $MethodUnit.method

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
