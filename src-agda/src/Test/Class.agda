
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

module Prop-Rel-Unit/Unit/Unit
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  = Rel-Unit/Unit/Unit (Extension 𝔓)

module UnitLevel-Unit/Unit/Unit
  {𝔬} (𝔒 : Ø 𝔬) (𝔯 : Ł)
  where
  private module M = Rel-Unit/Unit/Unit {𝔒 = 𝔒} {𝔯 = 𝔯}
  class = ∀ {ℜ} → M.class ℜ
  type = ∀ {ℜ} → M.type ℜ
  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ {ℜ = ℜ} = M.method ℜ ⦃ ⌶ {ℜ} ⦄ -- FIXME


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

module Prop-Rel-RelSingle/Rel/RelSingle
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  = Rel-RelSingle/Rel/RelSingle (Extension 𝔓)

module All-Prop-Rel-RelSingle/Rel/RelSingle (𝔬 𝔭 : Ł) where
  private module M = Prop-Rel-RelSingle/Rel/RelSingle
  class = ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → M.class 𝔓
  type = ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → M.type 𝔓
  method : ⦃ _ : class ⦄ → type
  method {𝔓 = 𝔓} = M.method 𝔓

module UnitLevel-RelSingle/Rel/RelSingle
  {𝔬} (𝔒 : Ø 𝔬) (𝔯 : Ł)
  where
  private module M = Rel-RelSingle/Rel/RelSingle {𝔒 = 𝔒} {𝔯 = 𝔯}
  class = ∀ {ℜ} → M.class ℜ
  type = ∀ {ℜ} → M.type ℜ
  method : ⦃ _ : class ⦄ → type
  method {ℜ = ℜ} = M.method ℜ


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

module Asymmetric
  ℓ
  (𝔓' : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) (x : 𝔒) → 𝔓 x → Ø ℓ)
  where
  module U = Unit-Unit/Unit/Unit
  test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y : 𝔓 x} → U.class (𝔓' 𝔓 x y) ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y : 𝔓 x} → U.class (𝔓' 𝔓 x y)
  test-class' = !

module Symmetric
  ℓ
  (𝔓' : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) (x : 𝔒) → 𝔓 x → 𝔓 x → Ø ℓ)
  where
  module U = Unit-Unit/Unit/Unit
  test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → U.class (𝔓' 𝔓 x y z → 𝔓' 𝔓 x y z) ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → U.class (𝔓' 𝔓 x y z → 𝔓' 𝔓 x y z)
  test-class' ⦃ ⌶ ⦄ = !
  module V {𝔬} (𝔒 : Ø 𝔬) = ℭlass (mkClass 𝔒 (𝔒 → 𝔒))
  test-classV : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → V.class (𝔓' 𝔓 x y z) ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → V.class (𝔓' 𝔓 x y z)
  test-classV ⦃ ⌶ ⦄ = !
  test-methodV : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → V.class (𝔓' 𝔓 x y z) ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} → V.type (𝔓' 𝔓 x y z)
  test-methodV ⦃ ⌶ ⦄ = V.method _
  module W {𝔬} {𝔒 : Ø 𝔬} (p : 𝔒) = ℭlass (mkClass p 𝔒)
  test-classW : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} {p : 𝔓' 𝔓 x y z} → W.class p ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} {p : 𝔓' 𝔓 x y z} → W.class p
  test-classW ⦃ ⌶ ⦄ = magic
  test-methodW : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} {p : 𝔓' 𝔓 x y z} → W.class p ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {x : 𝔒} {y z : 𝔓 x} {p : 𝔓' 𝔓 x y z} → W.type p
  test-methodW {p = p} = W.method p


module Prop-
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  module -Unit/Unit/Unit where
    module V = Prop-Unit/Unit/Unit 𝔓
    module H = Prop-Unit/Unit/Unit
    module X = Unit-Unit/Unit/Unit
    test-class' : ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓 ⦄ → {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓
    test-class' ⦃ ⌶ ⦄ {𝔓 = 𝔓} = magic -- ⌶ {𝔓 = 𝔓} -- FIXME
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
    test-class' : ⦃ _ : {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓 ⦄ → {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓
    test-class' ⦃ ⌶ ⦄ = magic
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

module Prop-Rel-
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  module -Unit/Unit/Unit where
    module V = Prop-Rel-Unit/Unit/Unit 𝔓
    module H = Prop-Rel-Unit/Unit/Unit
    module X = RelSingle-Unit/Unit/Unit
    test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓 ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓
    test-class' ⦃ ⌶ ⦄ {ℜ} = magic -- ! -- FIXME
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V ⦃ ⌶ ⦄ = magic
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H ⦃ ⌶ ⦄ = magic -- H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X ⦃ ⌶ ⦄ = magic -- X.method _ _
  module -RelSingle/Rel/RelSingle where
    module V = Prop-Rel-RelSingle/Rel/RelSingle 𝔓
    module H = Prop-Rel-RelSingle/Rel/RelSingle
    module X = RelSingle-RelSingle/Rel/RelSingle
    test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → H.class 𝔓 ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → H.class 𝔓
    test-class' ⦃ ⌶ ⦄ = !
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V ⦃ ⌶ ⦄ = magic -- V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H ⦃ ⌶ ⦄ = magic -- H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X ⦃ ⌶ ⦄ = magic -- FIXME

module UnitLevel-
  {𝔬} (𝔒 : Ø 𝔬) ℓ
  where
  module -Unit/Unit/Unit where
    module V = UnitLevel-Unit/Unit/Unit 𝔒 ℓ
    module H = UnitLevel-Unit/Unit/Unit
    module X = RelSingle-Unit/Unit/Unit
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class ⦃ ⌶ ⦄ {ℜ} = ⌶ {ℜ} -- FIXME
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V ⦃ ⌶ ⦄ {ℜ} = magic
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H ⦃ ⌶ ⦄ {ℜ} = magic -- H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X ⦃ ⌶ ⦄ {ℜ} x = magic -- X.method _ _
  module -RelSingle/Rel/RelSingle where
    module V = UnitLevel-RelSingle/Rel/RelSingle 𝔒 ℓ
    module H = UnitLevel-RelSingle/Rel/RelSingle
    module X = RelSingle-RelSingle/Rel/RelSingle
    test-class : ⦃ _ : V.class ⦄ → V.class
    test-class = !
    test-method-V : ⦃ _ : V.class ⦄ → V.type
    test-method-V ⦃ ⌶ ⦄ {ℜ} = magic -- V.method
    test-method-H : ⦃ _ : V.class ⦄ → V.type
    test-method-H ⦃ ⌶ ⦄ {ℜ} = magic -- H.method _
    test-method-X : ⦃ _ : V.class ⦄ → V.type
    test-method-X ⦃ ⌶ ⦄ {ℜ} = X.method ℜ _ -- FIXME

module Rel-Extension
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  (let ℜ = Extension 𝔓)
  where
  module -Unit/Unit/Unit where
    module V = Rel-Unit/Unit/Unit ℜ
    module H = Rel-Unit/Unit/Unit
    module X = Unit-Unit/Unit/Unit
    test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = Extension 𝔓) → H.class ℜ ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = Extension 𝔓) → H.class ℜ
    test-class' ⦃ ⌶ ⦄ {𝔓 = 𝔓} = magic -- ⌶ {𝔓 = 𝔓} -- FIXME
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
    test-class' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = Extension 𝔓) → H.class ℜ ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = Extension 𝔓) → H.class ℜ
    test-class' ⦃ ⌶ ⦄ = ! -- !
    test-class'' : ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = λ x _ → 𝔓 x) → H.class ℜ ⦄ → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} (let ℜ = λ x _ → 𝔓 x) → H.class ℜ
    test-class'' ⦃ ⌶ ⦄ = ! -- !
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
