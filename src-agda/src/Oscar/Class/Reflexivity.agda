
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data.𝟙

module Oscar.Class.Reflexivity where

module U
  {𝔬} {𝔒 : Ø 𝔬}
  = ℭLASS (mkClass 𝟙 𝔒)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private module M (x : 𝔒) = ℭLASS (mkClass _∼_ (x ∼ x))
  𝓡eflexivity = ∀ {x} → M.class x
  𝓻eflexivity = ∀ {x} → M.type x
  reflexivity[_] : ⦃ _ : 𝓡eflexivity ⦄ → 𝓻eflexivity
  reflexivity[_] = M.method _
  ε[_] = reflexivity[_]

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  reflexivity : {{_ : 𝓡eflexivity _∼_}} → 𝓻eflexivity _∼_
  reflexivity = reflexivity[ _∼_ ]
  ε = reflexivity

private

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔮} (𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔮)
    (y : 𝔒)
    where
    private module M (x : 𝔒) = ℭLASS (mkClass 𝔔 (𝔔 y x x))
    𝓡eflexivity' = ∀ {x} → M.class x
    𝓻eflexivity' = ∀ {x} → M.type x
    reflexivity'[_/_] : ⦃ _ : 𝓡eflexivity' ⦄ → 𝓻eflexivity'
    reflexivity'[_/_] = M.method _

  test-method : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    → 𝓻eflexivity _∼_
  test-method = reflexivity

  test-method' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯}
    ⦃ _ : {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity _∼_ ⦄
    → {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity _∼_
  test-method' {_∼_ = _∼_} = reflexivity[ _∼_ ]

  test-method′' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓡eflexivity (𝔔 y) ⦄
    → 𝓻eflexivity (𝔔 y)
  test-method′' = reflexivity

  test-method′ : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯}
    ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' 𝔔 y ⦄
    → ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' 𝔔 y
  test-method′ {y = y} {𝔔} = reflexivity'[ 𝔔 / y ]

  test-method'' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯}
    ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity (𝔔 y) ⦄
    → ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity (𝔔 y)
  test-method'' ⦃ ⌶ ⦄ {y = y} {𝔔} {x = x} = reflexivity ⦃ ⌶ {𝔔 = 𝔔} ⦄ -- FIXME

  test-method-ext : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
    ⦃ _ : 𝓡eflexivity (Extension 𝔓)  ⦄
    → 𝓻eflexivity (Extension 𝔓)
  test-method-ext = reflexivity

  test-method-ext' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭}
    ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → 𝓡eflexivity (Extension 𝔓)  ⦄
    → {𝔓 : 𝔒 → Ø 𝔭} → 𝓻eflexivity (Extension 𝔓)
  test-method-ext' {𝔓 = 𝔓} = reflexivity[ Extension 𝔓 ]

  test-method-ext′ : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭}
    ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → 𝓡eflexivity (λ x y → ∀ {z} → 𝔓 z → 𝔓 x → 𝔓 y)  ⦄
    → {𝔓 : 𝔒 → Ø 𝔭} → 𝓻eflexivity (λ x y → ∀ {z} → 𝔓 z → 𝔓 x → 𝔓 y)
  test-method-ext′ ⦃ ⌶ ⦄ {𝔓 = 𝔓} {x = x} =
    -- reflexivity ⦃ λ {x} → ⌶ {𝔓} {x = x} ⦄
    -- reflexivity[ (λ x y → ∀ {z} → 𝔓 z → 𝔓 x → 𝔓 y) ] ⦃ λ {x} → ⌶ {𝔓} {x} ⦄
    reflexivity[ (λ x y → ∀ {z} → 𝔓 z → 𝔓 x → 𝔓 y) ]
    -- reflexivity -- FIXME

  test-method-arrow : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭₁} {𝔓₁ : 𝔒 → Ø 𝔭₁}
    {𝔭₂} {𝔓₂ : 𝔒 → Ø 𝔭₂}
    ⦃ _ : 𝓡eflexivity (Arrow 𝔓₁ 𝔓₂) ⦄
    → 𝓻eflexivity (Arrow 𝔓₁ 𝔓₂)
  test-method-arrow = reflexivity

  test-method-arrow' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭}
    ⦃ _ : ∀ {x y} → 𝓡eflexivity (Arrow (𝔓 x) (𝔓 y))  ⦄
    → ∀ {x y} → 𝓻eflexivity (Arrow (𝔓 x) (𝔓 y))
  test-method-arrow' = reflexivity

  test-method-arrow'' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    ⦃ _ : ∀ {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭} {x y} → 𝓡eflexivity (Arrow (𝔓 x) (𝔓 y)) ⦄
    → ∀ {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭} {x y} → 𝓻eflexivity (Arrow (𝔓 x) (𝔓 y))
  test-method-arrow'' ⦃ ⌶ ⦄ {𝔓 = 𝔓} {x} {y} = reflexivity[ Arrow (𝔓 x) (𝔓 y) ] ⦃ ⌶ {𝔓 = 𝔓} ⦄ -- FIXME

  test-class : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    → 𝓡eflexivity _∼_
  test-class = !

  test-class-quantified :
    ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity _∼_ ⦄
    → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity _∼_
  test-class-quantified ⦃ ⌶ ⦄ = !

  test-class-ext :
    ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → 𝓡eflexivity (Extension 𝔓) ⦄
    → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → 𝓡eflexivity (Extension 𝔓)
  test-class-ext ⦃ ⌶ ⦄ = !
