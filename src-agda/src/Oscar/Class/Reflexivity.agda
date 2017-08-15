
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private module M (x : 𝔒) = ℭLASS _∼_ (x ∼ x)
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
    private module M = ℭLASS _∼_ (x ∼ x)
    ⟦_/_⟧ = M.class
    ⟨_/_⟩ = M.type
    [_/_] = M.method
  module _
    {x : 𝔒} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M = ℭLASS _∼_ (x ∼ x)
    [_] = M.method
  module _
    (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M x = ℭLASS _∼_ (x ∼ x)
    ⟦_⟧ = ∀ {x} → M.class x
    ⟨_⟩ = ∀ {x} → M.type x
  module _
    {x : 𝔒} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    where
    private module M = ℭLASS _∼_ (x ∼ x)
    [] = M.method

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {x : 𝔒}
  ⦃ particular : Refl.⟦ x / _∼_ ⟧ ⦄
  ⦃ general : Refl.⟦ _∼_ ⟧ ⦄
  ⦃ very-general : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {x : 𝔒} → Refl.⟦ x / _∼_ ⟧ ⦄
  where

  private

    very-general-class : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟦ _∼_ ⟧
    very-general-class = !

    very-general-type : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟨ _∼_ ⟩
    very-general-type {_∼_ = _∼_} = Refl.[ _∼_ ]

    general-class : Refl.⟦ _∼_ ⟧
    general-class = magic -- FIXME cannot find b/c of very-general

    particular-type : Refl.⟨ x / _∼_ ⟩
    particular-type = magic -- FIXME cannot find b/c of general

module _
  ⦃ very-general : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟦ _∼_ ⟧ ⦄
  where

  private

    very-general-type : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟨ _∼_ ⟩
    very-general-type {_∼_ = _∼_} = Refl.[ _∼_ ]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {_∼'_ : 𝔒 → 𝔒 → Ø 𝔯} {x : 𝔒}
  ⦃ particular : Refl.⟦ x / _∼_ ⟧ ⦄
  ⦃ general : Refl.⟦ _∼_ ⟧ ⦄
  ⦃ general' : Refl.⟦ _∼'_ ⟧ ⦄
  where

  module _ where

    private

      general-class : Refl.⟦ _∼_ ⟧
      general-class = !

      general-type : Refl.⟨ _∼_ ⟩
      general-type = Refl.[]

  module _
    ⦃ more-general : {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟦ _∼_ ⟧ ⦄
    where

    private

      general-class : Refl.⟦ _∼_ ⟧
      general-class = magic

      general-type : Refl.⟨ _∼_ ⟩
      general-type = magic

      more-general-class : {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟦ _∼_ ⟧
      more-general-class = !

      more-general-type : {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟨ _∼_ ⟩
      more-general-type {_∼_} = Refl.[ _∼_ ]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯} {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : Refl.⟦ 𝔔 y ⟧ ⦄
  where

  private

    class : Refl.⟦ 𝔔 y ⟧
    class = !

    type : Refl.⟨ 𝔔 y ⟩
    type = Refl.[]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : ∀ {y} → Refl.⟦ 𝔔 y ⟧ ⦄
  {y}
  where

  private

    class : Refl.⟦ 𝔔 y ⟧
    class = !

    type : Refl.⟨ 𝔔 y ⟩
    type = Refl.[]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : {ℜ : 𝔒 → Ø 𝔯} → Refl.⟦ F ℜ ⟧ ⦄
  {ℜ : 𝔒 → Ø 𝔯}
  where

  private

    class : Refl.⟦ F ℜ ⟧
    class = !

    type : Refl.⟨ F ℜ ⟩
    type = Refl.[]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔯}
  ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl.⟦ 𝔔 y ⟧ ⦄
  {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
  where

  private

    general-class : Refl.⟦ 𝔔 y ⟧
    general-class = magic

    general-type : Refl.⟨ 𝔔 y ⟩
    general-type = magic

    particular-class : Refl.⟦ y / 𝔔 y ⟧
    particular-class = magic

    particular-type : Refl.⟨ y / 𝔔 y ⟩
    particular-type = magic

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  ⦃ particular : Refl.⟦ Extension 𝔓 ⟧  ⦄
  where

  module _ where

    private

      class : Refl.⟦ Extension 𝔓 ⟧
      class = !

      type : Refl.⟨ Extension 𝔓 ⟩
      type = Refl.[]

  module _
    ⦃ general : {𝔓 : 𝔒 → Ø 𝔭} → Refl.⟦ Extension 𝔓 ⟧  ⦄
    {𝔓' : 𝔒 → Ø 𝔭}
    where

    private

      class : Refl.⟦ Extension 𝔓 ⟧
      class = magic

      class' : Refl.⟦ Extension 𝔓' ⟧
      class' = !

      type : Refl.⟨ Extension 𝔓 ⟩
      type = magic -- both particular and general are candidates

      type' : Refl.⟨ Extension 𝔓' ⟩
      type' = Refl.[ Extension 𝔓' ] -- only general is candidate b/c 𝔓' does not unify with 𝔓

      open import Oscar.Data.Proposequality

      type'noeq : 𝔓' ≡ 𝔓 → Refl.⟨ Extension 𝔓' ⟩
      type'noeq x = Refl.[ Extension 𝔓' ] -- still works

      type'eq : 𝔓' ≡ 𝔓 → Refl.⟨ Extension 𝔓' ⟩
      type'eq ∅ = magic -- both particular and general are candidates

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭}
  (let F : (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø _
       F 𝔓 x y = ∀ {z} → 𝔓 z → 𝔓 x → 𝔓 y)
  (let F' : (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø _
       F' 𝔓 x y = ∀ {z} → 𝔓 x → 𝔓 z → 𝔓 y)
  (let F'' : (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø _
       F'' 𝔓 x y = ∀ {z} → 𝔓 y → 𝔓 z → 𝔓 x)
  ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → Refl.⟦ F 𝔓 ⟧  ⦄
  ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → Refl.⟦ F' 𝔓 ⟧  ⦄
  ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → Refl.⟦ F'' 𝔓 ⟧  ⦄
  {𝔓 : 𝔒 → Ø 𝔭}
  where

  private

    class : Refl.⟦ F 𝔓 ⟧
    class = !

    type : Refl.⟨ F 𝔓 ⟩
    type = Refl.[ (λ _ _ → ∀ {z} → 𝔓 z → _) ]
    {-
      𝔓 .z → 𝔓 x → 𝔓 x ≟ _Q _x _x -- goal ≟ have
      _Q _x _x ≟ (∀ {z} → _𝔓' z → _𝔓' _x' → _𝔓' _x') -- haveM ≟ instanceM
      _Q ≟ (λ x y → ∀ {z} → _𝔓' z → _𝔓' x → _𝔓' y) -- haveC ≟ instanceC
      (∀ {z} → _𝔓' z → _𝔓' _x → _𝔓' _x) ≟ (∀ {z} → _𝔓' z → _𝔓' _x' → _𝔓' _x') -- derived
      _x ≟ _x' -- derived
      _Q ≟ (λ _ _ → ∀ {z} → 𝔓 z → _) -- user argument
      (λ _ _ → ∀ {z} → 𝔓 z → _) ≟ (λ x y → ∀ {z} → _𝔓' z → _𝔓' x → _𝔓' y) -- derived
      (∀ {z} → 𝔓 z) ≟ (∀ {z} → _𝔓' z) -- derived
      𝔓 ≟ _𝔓' -- derived
    -}

    class' : Refl.⟦ F' 𝔓 ⟧
    class' = !

    type' : Refl.⟨ F' 𝔓 ⟩
    type' = Refl.[ (λ _ y → ∀ {z} → 𝔓 y → 𝔓 z → _) ]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭₁} {𝔓₁ : 𝔒 → Ø 𝔭₁} {𝔭₂} {𝔓₂ : 𝔒 → Ø 𝔭₂}
  ⦃ _ : Refl.⟦ Arrow 𝔓₁ 𝔓₂ ⟧ ⦄
  where

  private

    class : Refl.⟦ Arrow 𝔓₁ 𝔓₂ ⟧
    class = !

    type : Refl.⟨ Arrow 𝔓₁ 𝔓₂ ⟩
    type = Refl.[]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭}
  ⦃ _ : ∀ {x y} → Refl.⟦ Arrow (𝔓 x) (𝔓 y) ⟧ ⦄
  {x y}
  where

  private

    class : Refl.⟦ Arrow (𝔓 x) (𝔓 y) ⟧
    class = !

    type : Refl.⟨ Arrow (𝔓 x) (𝔓 y) ⟩
    type = Refl.[]

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭}
  ⦃ _ : ∀ {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭} {x y} → Refl.⟦ Arrow (𝔓 x) (𝔓 y) ⟧ ⦄
  {𝔭} {𝔓 : 𝔒 → 𝔒 → Ø 𝔭} {x y}
  where

  private

    class : Refl.⟦ Arrow (𝔓 x) (𝔓 y) ⟧
    class = magic

    type : Refl.⟨ Arrow (𝔓 x) (𝔓 y) ⟩
    type = magic

private

  module Refl'
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔮} (𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔮)
    (y : 𝔒)
    where
    private module M (x : 𝔒) = ℭLASS 𝔔 (𝔔 y x x)
    ⟦_/_⟧ = ∀ {x} → M.class x
    ⟨_/_⟩ = ∀ {x} → M.type x
    [_/_] : ⦃ _ : ⟦_/_⟧ ⦄ → ⟨_/_⟩
    [_/_] = M.method _

  instance

    ReflFromRefl' : ∀
      {𝔬} {𝔒 : Ø 𝔬}
      {𝔮} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔮}
      {y : 𝔒}
      ⦃ _ : Refl'.⟦ 𝔔 / y ⟧ ⦄
      → Refl.⟦ 𝔔 y ⟧
    ReflFromRefl' .⋆ = Refl'.[ _ / _ ]

  test-method1′ : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : Refl'.⟦ 𝔔 / y ⟧ ⦄
    → Refl'.⟨ 𝔔 / y ⟩
  test-method1′ = Refl.[]

  test-method1′'' : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : Refl'.⟦ 𝔔 / y ⟧ ⦄
    → Refl'.⟨ 𝔔 / y ⟩
  test-method1′'' = Refl'.[ _ / _ ]

  test-method1′' : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} → Refl'.⟦ 𝔔 / y ⟧ ⦄
    → ∀ {y} → Refl'.⟨ 𝔔 / y ⟩
  test-method1′' = Refl'.[ _ / _ ]

  test-method′2 : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {ℜ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ F ℜ / y ⟧ ⦄
    → ∀ {y} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ F ℜ / y ⟩
  test-method′2 {ℜ = ℜ} {{i}} {y = y} {F} {x} = Refl'.[_/_] _ _ {{i {F = F}}}
  {-
    F R y x x = _Q _y _x _x = _F' R _y' _x' _x' [ F ℜ / y ]
    _F' R = _Q
    _Q = F R ; _y = y

    F R y x x = F R _y _x _x
    _y = y
    _x = x
    _F' = ?
  -}

  test-method′3 : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ F ℜ / y ⟧ ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ F ℜ / y ⟩
  test-method′3 {F = F} {{i}} {y = y} {ℜ} = Refl'.[ _ / _ ]

  test-method′4 : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ F ℜ / y ⟧ ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ F ℜ / y ⟩
  test-method′4 {F = F} {{i}} {y = y} {ℜ} = Refl'.[ _ / _ ]

  test-method′5 : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ ℜ / y ⟧ ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ ℜ / y ⟩
  test-method′5 {F = F} {{i}} {y = y} {ℜ} = Refl'.[ ℜ / _ ]
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
    {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ F ℜ / y ⟧ ⦄
    → ∀ {y} {ℜ : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ F ℜ / y ⟩
  test-method′5' {F = F} {{i}} {y = y} {ℜ} = Refl'.[ _ / _ ]
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

  test-method′ : ∀
    {𝔬} {𝔒 : Ø 𝔬} {𝔯}
    ⦃ _ : ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟦ 𝔔 / y ⟧ ⦄
    → ∀ {y} {𝔔 : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Refl'.⟨ 𝔔 / y ⟩
  test-method′ {𝔔 = 𝔔} = Refl'.[ 𝔔 / _ ]
