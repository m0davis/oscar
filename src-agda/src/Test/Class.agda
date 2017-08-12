
open import Oscar.Prelude
open import Oscar.Data.Constraint
open import Oscar.Data.𝟙

module Test.Class where

record ℭlass
  {ℓ}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  (constraints : CONSTRAINTS)
  : Ø ↑̂ ℓ
  where
  constructor ∁
  field
    type : Ø ℓ
  private
    record SET-CLASS
      ⦃ _ : Constraint constraints ⦄
      : Ø ℓ
      where
      constructor ∁
      field ⋆ : type
  open SET-CLASS public
  class : Ø _
  class = SET-CLASS
  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶

mkClass : ∀
  {ℓ}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  (constraints : CONSTRAINTS)
  → Ø ℓ
  → ℭlass constraints
mkClass constraints set-method = ∁ set-method


module Unit-Unit/Unit/Unit
  {𝔬} (𝔒 : Ø 𝔬)
  = ℭlass (mkClass 𝔒 𝔒)

module PropSingle-Unit/Unit/Unit
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  (x : 𝔒)
  = Unit-Unit/Unit/Unit (𝔓 x)

module Prop-Unit/Unit/Unit
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  private module M = PropSingle-Unit/Unit/Unit 𝔓
  class = ∀ {x} → M.class x
  type = ∀ x → M.type x
  method = λ ⦃ _ : class ⦄ x → M.method x

module RelSingle-Unit/Unit/Unit
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  (x : 𝔒)
  = Unit-Unit/Unit/Unit (ℜ x x)

module Rel-Unit/Unit/Unit
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private module M = RelSingle-Unit/Unit/Unit ℜ
  class = ∀ {x} → M.class x
  type = ∀ x → M.type x
  method = λ ⦃ _ : class ⦄ x → M.method x


module RelSingle-RelSingle/Rel/RelSingle
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  (x : 𝔒)
  = ℭlass (mkClass ℜ (ℜ x x))

module Rel-RelSingle/Rel/RelSingle
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private module M = RelSingle-RelSingle/Rel/RelSingle ℜ
  class = ∀ {x} → M.class x
  type = ∀ {x} → M.type x
  method = λ ⦃ _ : class ⦄ {x} → M.method x


module PropSingle-PropSingle/Prop/PropSingle
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  (x : 𝔒)
  where
  open ℭlass (mkClass 𝔓 (𝔓 x)) public

module Prop-PropSingle/Prop/PropSingle
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  private module M = PropSingle-PropSingle/Prop/PropSingle 𝔓
  class = ∀ {x} → M.class x
  type = ∀ x → M.type x
  method = λ ⦃ _ : class ⦄ x → M.method x


module Prop-
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  module -Unit/Unit/Unit where
    module V = Prop-Unit/Unit/Unit 𝔓
    module H = Prop-Unit/Unit/Unit
    module X = Unit-Unit/Unit/Unit
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V = V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H = H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X _ = X.method _ -- FIXME
  module -PropSingle/Prop/PropSingle where
    module V = Prop-PropSingle/Prop/PropSingle 𝔓
    module H = Prop-PropSingle/Prop/PropSingle
    module X = PropSingle-PropSingle/Prop/PropSingle
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V = V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H = H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X _ = X.method _ _ -- FIXME

module Rel-
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  module -Unit/Unit/Unit where
    module V = Rel-Unit/Unit/Unit ℜ
    module H = Rel-Unit/Unit/Unit
    module X = Unit-Unit/Unit/Unit
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V = V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H = H.method ℜ -- FIXME
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X _ = X.method _ -- FIXME
  module -RelSingle/Rel/RelSingle where
    module V = Rel-RelSingle/Rel/RelSingle ℜ
    module H = Rel-RelSingle/Rel/RelSingle
    module X = RelSingle-RelSingle/Rel/RelSingle
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V = V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H = H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X = X.method _ _

module AllUnitTest where
  test : ⦃ I : ∀ {𝔬} {𝔒 : Ø 𝔬} → Unit-Unit/Unit/Unit.class 𝔒 ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} → Unit-Unit/Unit/Unit.class 𝔒
  test = !

module AllTest
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭}
  where

  testProp : ⦃ I : {𝔓 : 𝔒 → Ø 𝔭} → Prop-PropSingle/Prop/PropSingle.class 𝔓 ⦄ → {𝔓 : 𝔒 → Ø 𝔭} → Prop-PropSingle/Prop/PropSingle.class 𝔓
  testProp = !

  testUnitProp : ⦃ I : {𝔓 : 𝔒 → Ø 𝔭} → Prop-Unit/Unit/Unit.class 𝔓 ⦄ → {𝔓 : 𝔒 → Ø 𝔭} → Prop-Unit/Unit/Unit.class 𝔓
  testUnitProp ⦃ I ⦄ {𝔓} = I {𝔓}

module SinglePropTest
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where

  testProp : ⦃ _ : Prop-PropSingle/Prop/PropSingle.class 𝔓 ⦄ → Prop-PropSingle/Prop/PropSingle.class 𝔓
  testProp = !

  testUnitProp : ⦃ _ : Prop-Unit/Unit/Unit.class 𝔓 ⦄ → Prop-Unit/Unit/Unit.class 𝔓
  testUnitProp = !

module SingleRelTest
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (ℜ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  testProp : ⦃ _ : Rel-RelSingle/Rel/RelSingle.class ℜ ⦄ → Rel-RelSingle/Rel/RelSingle.class ℜ
  testProp = !
  testUnit : ⦃ _ : Rel-Unit/Unit/Unit.class ℜ ⦄ → Rel-Unit/Unit/Unit.class ℜ
  testUnit = !
