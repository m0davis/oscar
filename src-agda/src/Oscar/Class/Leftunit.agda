
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.Leftunit where

module Leftunit
  {𝔞 𝔟} {𝔄 : Ø 𝔞} {𝔅 : Ø 𝔟}
  {𝔢} {𝔈 : Ø 𝔢}
  {𝔞𝔟}
  (_↤_ : 𝔅 → 𝔄 → Ø 𝔞𝔟) (let _↤_ = _↤_; infix 4 _↤_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔅) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  = ℭLASS (ε , _◃_ , _↤_) (ε ◃ x ↤ x)

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  {x : 𝔄}
  where
  leftunit = Leftunit.method _↦_ ε _◃_ x

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

open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjection
open import Oscar.Class.Smap

module Leftunit,smaparrow
  {𝔵₁ 𝔵₂ 𝔭₁ 𝔭₂ 𝔯 𝔭̇₁₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : π̂² 𝔯 𝔛₁)
  (𝔓₁ : π̂ 𝔭₁ 𝔛₂)
  (𝔓₂ : π̂ 𝔭₂ 𝔛₂)
  (ε : Reflexivity.type ℜ)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  (smaparrow : Smaparrow.type ℜ 𝔓₁ 𝔓₂ surjection surjection)
  (𝔓̇₁₂ : ∀ {x} → 𝔓₁ (surjection x) → 𝔓₂ (surjection x) → Ø 𝔭̇₁₂)
  where
  class = ∀ {x} {p : 𝔓₁ (surjection x)} → Leftunit.class (flip 𝔓̇₁₂) ε smaparrow p
  type = ∀ {x} {p : 𝔓₁ (surjection x)} → Leftunit.type (flip 𝔓̇₁₂) ε smaparrow p
  method : ⦃ _ : class ⦄ → type
  method {x} {p} = Leftunit.method (flip 𝔓̇₁₂) ε smaparrow p

module Leftunit,smaparrow!
  {𝔵₁ 𝔵₂ 𝔭₁ 𝔭₂ 𝔯 𝔭̇₁₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : π̂² 𝔯 𝔛₁)
  (𝔓₁ : π̂ 𝔭₁ 𝔛₂)
  (𝔓₂ : π̂ 𝔭₂ 𝔛₂)
  ⦃ _ : Reflexivity.class ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaparrow!.class ℜ 𝔓₁ 𝔓₂ ⦄
  (𝔓̇₁₂ : ∀ {x} → 𝔓₁ (surjection x) → 𝔓₂ (surjection x) → Ø 𝔭̇₁₂)
  = Leftunit,smaparrow ℜ 𝔓₁ 𝔓₂ ε surjection smaparrow 𝔓̇₁₂

module Leftunit,smaphomarrow
  {𝔵₁ 𝔵₂ 𝔭 𝔯 𝔭̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : π̂² 𝔯 𝔛₁)
  (𝔓 : π̂ 𝔭 𝔛₂)
  (ε : Reflexivity.type ℜ)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  (smaparrow : Smaphomarrow.type ℜ 𝔓 surjection)
  (𝔓̇ : ∀ {x} → 𝔓 (surjection x) → 𝔓 (surjection x) → Ø 𝔭̇)
  = Leftunit,smaparrow ℜ 𝔓 𝔓 ε surjection smaparrow 𝔓̇

module Leftunit,smaphomarrow!
  {𝔵₁ 𝔵₂ 𝔭 𝔯 𝔭̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : π̂² 𝔯 𝔛₁)
  (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : Reflexivity.class ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  (𝔓̇ : ∀ {x} → 𝔓 (surjection x) → 𝔓 (surjection x) → Ø 𝔭̇)
  = Leftunit,smaphomarrow ℜ 𝔓 ε surjection smaparrow 𝔓̇

open import Oscar.Class.HasEquivalence

module Leftunit,equivalence,smaphomarrow!
  {𝔵₁ 𝔵₂ 𝔭 𝔯 𝔭̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : π̂² 𝔯 𝔛₁)
  (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : Reflexivity.class ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) 𝔭̇ ⦄
  = Leftunit,smaphomarrow! ℜ 𝔓 _≈_
