
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
  P𝔩eftunit = 𝔩eftunit

module LeftunitAllxHiddenCtr
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  private module ∁ = Leftunit _↦_ ε _◃_
  private
    c𝒄tr : ∀ {ℓ} → (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    c𝒄tr f = ∀ {x} → f x
    m𝒄tr : ∀ {ℓ} → (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    m𝒄tr f = ∀ {x} → f x
  𝒄lass = c𝒄tr ∁.𝒄lass
  𝒕ype = m𝒄tr ∁.𝒕ype
  𝒎ethod : ⦃ _ : 𝒄lass ⦄ → 𝒕ype
  𝒎ethod {x = x} = ∁.𝒎ethod x

module LeftunitAllxVisibleCtr
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  private module ∁ = Leftunit _↦_ ε _◃_
  private
    c𝒄tr : ∀ {ℓ} → (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    c𝒄tr f = ∀ {x} → f x
    m𝒄tr : ∀ {ℓ} → (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    m𝒄tr f = ∀ x → f x
  𝒄lass = c𝒄tr ∁.𝒄lass
  𝒕ype = m𝒄tr ∁.𝒕ype
  𝒎ethod : ⦃ _ : 𝒄lass ⦄ → 𝒕ype
  𝒎ethod x = ∁.𝒎ethod x

module MLeftunit
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  where
  module _
    (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
    (ε : 𝔈)
    (_◃_ : 𝔈 → 𝔄 → 𝔄)
    (x : 𝔄)
    where
    private module M = ℭLASS (Leftunit.P𝔩eftunit _↦_ ε _◃_ x)
    𝒄lass = M.𝒄lass
    𝒕ype = M.𝒕ype
  module _
    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
    {ε : 𝔈}
    {_◃_ : 𝔈 → 𝔄 → 𝔄}
    {x : 𝔄}
    where
    private module M = ℭLASS (Leftunit.P𝔩eftunit _↦_ ε _◃_ x)
    𝒎ethod = M.𝒎ethod

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
