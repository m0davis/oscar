
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

module Factsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔓 : π̂ 𝔭 𝔛₂)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛₁)
  (ε : 𝓻eflexivity ℜ)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  (_◃_ : Smaphomarrow!.type ℜ 𝔓 ⦃ ∁ surjection ⦄)
  where
  class = ∀ {x} {p : 𝔓 (surjection x)} → Leftunit.class (flip (_≈_ {surjection x})) ε _◃_ p
  type = ∀ {x} {p : 𝔓 (surjection x)} → Leftunit.type (flip (_≈_ {surjection x})) ε _◃_ p
  method : ∀ {x} {p : 𝔓 (surjection x)} → ⦃ _ : Leftunit.class (flip (_≈_ {surjection x})) ε _◃_ p ⦄ → Leftunit.type (flip (_≈_ {surjection x})) ε _◃_ p
  method = leftunit

open import Oscar.Class.HasEquivalence

module 𝓕actsurj3
  {𝔵₁ 𝔵₂ 𝔭 𝔯 ℓ} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  (ℜ : π̂² 𝔯 𝔛₁)
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  = Factsurj3 𝔓 _≈_ ℜ ε surjection smaparrow
