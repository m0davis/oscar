
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

module $ClassSingle
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  (x : 𝔄)
  where
  private module M = ℭLASS ($Family.family _↦_ ε _◃_ x)
  class = M.𝒄lass
  type = M.𝒕ype
  method = M.𝒎ethod

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
  private module M = ℭLASS ($Family.family _↦_ ε _◃_ x)
  method = M.𝒎ethod

module $MethodAll
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  private module M = $ClassAll _↦_ ε _◃_
  method = M.method

{-
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x : 𝔄)
  where
  private module M = ℭLASS (ℭlass (ε , _◃_ , _↦_) ∋ (∁ $′ ε ◃ x ↦ x))
  𝒕ype = m𝒄tr ∁.𝒕ype
  𝒎ethod : ⦃ _ : 𝒄lass ⦄ → 𝒕ype
  𝒎ethod {x = x} = ∁.𝒎ethod x
-}

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
  𝓛eftunit = 𝒄lass

module LeftunitAllUseClass
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  where
  𝔩eftunitAll : ℭlass (ε , _◃_ , _↦_)
  𝔩eftunitAll = ∁ $′ ∀ x → ε ◃ x ↦ x
  open ℭLASS 𝔩eftunitAll public

module LeftunitAllUseClassHidden
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  where
  𝔩eftunitAll : ℭlass (ε , _◃_ , _↦_)
  𝔩eftunitAll = ∁ $′ ∀ {x} → ε ◃ x ↦ x
  open ℭLASS 𝔩eftunitAll public

module Single = Leftunit
module All = LeftunitAllUseClass
module HAll = LeftunitAllUseClassHidden

instance

  allToSingles : ∀
    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
    {ε : 𝔈}
    {_◃_ : 𝔈 → 𝔄 → 𝔄}
    ⦃ _ : All.𝒄lass _↦_ ε _◃_ ⦄
    → ∀ {x} → Single.𝒄lass _↦_ ε _◃_ x
  allToSingles {x = x} .⋆ = All.𝒎ethod _ _ _ hid

  HallToSingles : ∀
    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
    {ε : 𝔈}
    {_◃_ : 𝔈 → 𝔄 → 𝔄}
    ⦃ _ : HAll.𝒄lass _↦_ ε _◃_ ⦄
    → ∀ {x} → Single.𝒄lass _↦_ ε _◃_ x
  HallToSingles {x = x} .⋆ = HAll.𝒎ethod _ _ _ -- {x = x}

--  allToSingles' : ∀
--    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
--    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
--    {ε : 𝔈}
--    {_◃_ : 𝔈 → 𝔄 → 𝔄}
--    ⦃ _ : ∀ {x} → Single.𝒄lass _↦_ ε _◃_ x ⦄
--    → All.𝒄lass _↦_ ε _◃_
--  allToSingles' .⋆ x = Single.𝒎ethod _ _ _ x
--
--  allToSingles'Hidden : ∀
--    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
--    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
--    {ε : 𝔈}
--    {_◃_ : 𝔈 → 𝔄 → 𝔄}
--    ⦃ _ : ∀ {x} → Single.𝒄lass _↦_ ε _◃_ x ⦄
--    → HAll.𝒄lass _↦_ ε _◃_
--  allToSingles'Hidden .⋆ {x = x} = Single.𝒎ethod _ _ _ x

module Test
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ) (let _↦_ = _↦_; infix 4 _↦_)
  (ε1 : 𝔈)
  (ε2 : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄) (let _◃_ = _◃_; infix 16 _◃_)
  (x1 x2 : 𝔄)
  ⦃ _ : ∀ {x3} → Single.𝒄lass _↦_ ε1 _◃_ x3 ⦄
  -- ⦃ _ : ∀ {x3} → $ClassSingle.Class _↦_ ε1 _◃_ x3 ⦄
  ⦃ _ : $ClassAll.class _↦_ ε1 _◃_ ⦄
  ⦃ _ : Single.𝒄lass _↦_ ε1 _◃_ x2 ⦄
  ⦃ _ : All.𝒄lass _↦_ ε2 _◃_ ⦄
  -- ⦃ _ : HAll.𝒄lass _↦_ ε2 _◃_ ⦄
  -- ⦃ _ : All.𝒄lass _↦_ ε1 _◃_ ⦄

  where

  test1 : Single.𝒕ype _↦_ ε1 _◃_ x1
  test1 = Single.𝒎ethod _ _ _ _

  test1' : $ClassAll.type _↦_ ε1 _◃_
  test1' x = $MethodSingle.method

  -- test1'' : All.𝒕ype _↦_ ε1 _◃_
  -- test1'' = All.𝒎ethod _ _ _

  test2 : All.𝒕ype _↦_ ε2 _◃_
  test2 = All.𝒎ethod _ _ _

  test2' : All.𝒕ype _↦_ ε2 _◃_
  test2' x = Single.𝒎ethod _↦_ ε2 _◃_ x -- Single.𝒎ethod _ _ _




module LeftunitAllxHiddenCtr
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  private module ∁ = Leftunit _↦_ ε _◃_
  private
    c𝒄tr : (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    c𝒄tr f = ∀ {x} → f x
    m𝒄tr : (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
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
    c𝒄tr : (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
    c𝒄tr f = ∀ {x} → f x
    m𝒄tr : (𝔄 → Ø ℓ) → Ø 𝔞 ∙̂ ℓ
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
