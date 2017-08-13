
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

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

module Refl
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯}
  where
  module _
    (x : 𝔒) (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M = ℭLASS (mkClass _∼_ (x ∼ x))
    ⟦_/_⟧ = M.class
    ⟨_/_⟩ = M.type
    [_/_] = M.method
  module _
    {x : 𝔒} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M = ℭLASS (mkClass _∼_ (x ∼ x))
    [_] = M.method
  module _
    (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M x = ℭLASS (mkClass _∼_ (x ∼ x))
    ⟦_⟧ = ∀ {x} → M.class x
    ⟨_⟩ = ∀ {x} → M.type x
  module _
    {x : 𝔒} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    where
    private module M = ℭLASS (mkClass _∼_ (x ∼ x))
    [] = M.method

private

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    (x : 𝔒)
    where
    private module M = ℭLASS (mkClass _∼_ (x ∼ x))
    𝓡eflSingle = M.class
    𝓻eflSingle = M.type
    reflSingle[_/_] : ⦃ _ : 𝓡eflSingle ⦄ → 𝓻eflSingle
    reflSingle[_/_] = M.method

  test-class-single :
    ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {x : 𝔒} → 𝓡eflSingle _∼_ x ⦄
    → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {x : 𝔒} → 𝓡eflSingle _∼_ x
  test-class-single ⦃ ⌶ ⦄ = !

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

  test-method1′ : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓡eflexivity' 𝔔 y ⦄
    → 𝓻eflexivity' 𝔔 y
  test-method1′ = reflexivity'[ _ / _ ]

  test-method1′' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} → 𝓡eflexivity' 𝔔 y ⦄
    → ∀ {y} → 𝓻eflexivity' 𝔔 y
  test-method1′' = reflexivity'[ _ / _ ]

  test-method′2 : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {ℜ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' (F ℜ) y ⦄
    → ∀ {y} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' (F ℜ) y
  test-method′2 {ℜ = ℜ} {{i}} {y = y} {F} {x} = reflexivity'[_/_] _ _ {{i {F = F}}}
  {-
    F R y x x = _Q _y _x _x = _F' R _y' _x' _x' reflexivity'[ F ℜ / y ]
    _F' R = _Q
    _Q = F R ; _y = y

    F R y x x = F R _y _x _x
    _y = y
    _x = x
    _F' = ?
  -}

  test-method′3 : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' (F ℜ) y ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' (F ℜ) y
  test-method′3 {F = F} {{i}} {y = y} {ℜ} = reflexivity'[ _ / _ ]

  test-method′4 : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' (F ℜ) y ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' (F ℜ) y
  test-method′4 {F = F} {{i}} {y = y} {ℜ} = reflexivity'[ _ / _ ]

  test-method′5 : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' ℜ y ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' ℜ y
  test-method′5 {F = F} {{i}} {y = y} {ℜ} = reflexivity'[ ℜ / _ ]
  {-
    target: R y .x .x = _Q _y _x _x = _R' _y' _x' _x'
    constr: _Q = _R'
    params: _Q = R

    _y = _y'
    _x = _x'

    _y = y
    _x = .x
  -}

  test-method′5' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' (F ℜ) y ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' (F ℜ) y
  test-method′5' {F = F} {{i}} {y = y} {ℜ} = reflexivity'[ _ / _ ]
  {-
    target: F R y .x .x = _Q _y _x _x = F _R' _y' _x' _x'
    constr: _Q = F _R'

    _R' = R
    _y' = y
    _x' = .x
    _Q = F R
    _y = y
    _x = .x

    target: goal = method = instance
    constr: methodconstraint = instanceconstraint
  -}

  test-method3 : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {F : (𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : {ℜ : 𝔒 → Ø 𝔯} → 𝓡eflexivity (F ℜ) ⦄
    → ∀ {ℜ : 𝔒 → Ø 𝔯} → 𝓻eflexivity (F ℜ)
  test-method3 = reflexivity

  test-method′ : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯}
    ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity' 𝔔 y ⦄
    → ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity' 𝔔 y
  test-method′ {𝔔 = 𝔔} = reflexivity'[ 𝔔 / _ ]

  test-method'' : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯}
    ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓡eflexivity (𝔔 y) ⦄
    → ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → 𝓻eflexivity (𝔔 y)
  test-method'' ⦃ ⌶ ⦄ {y = y} {𝔔} {x = x} = reflexivity ⦃ ⌶ {𝔔 = 𝔔} ⦄ -- FIXME
  {-
    Q y x x = _R _x _x = _Q' _y' _x' _x'
    _R = _Q' _y'
    _R = Q y <-- from reflexivity[ Q y ]

    Q y x x = Q y _x _x
    _x = x
  -}

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
