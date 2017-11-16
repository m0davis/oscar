
module Oscar.Category where

open import Oscar.Level
open import Oscar.Function

record Setoid {𝔬} (𝔒 : Ø 𝔬) 𝔮 : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
  infix 4 _≋_
  field
    _≋_ : 𝔒 → 𝔒 → Ø 𝔮
    ≋-reflexivity : ∀ {x} → x ≋ x
    ≋-symmetry : ∀ {x y} → x ≋ y → y ≋ x
    ≋-transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

record Semigroupoid
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
  {𝔮} (𝔐-setoid : ∀ {x y} → Setoid (𝔐 x y) 𝔮)
  : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮 where
  instance _ = λ {x y} → 𝔐-setoid {x} {y}
  open Setoid ⦃ … ⦄ using (_≋_)
  infixr 9 _∙_
  field
    _∙_ : ∀ {y z} → 𝔐 y z → ∀ {x} → 𝔐 x y → 𝔐 x z
    ∙-extensionality : ∀ {x y} {f₁ f₂ : 𝔐 x y} → f₁ ≋ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
    ∙-associativity : ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → (h ∙ g) ∙ f ≋ h ∙ (g ∙ f)

record Category
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔪} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
  {𝔮} {𝔐-setoid : ∀ {x y} → Setoid (𝔐 x y) 𝔮}
  (semigroupoid : Semigroupoid 𝔐 𝔐-setoid)
  : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮 where
  instance _ = λ {x y} → 𝔐-setoid {x} {y}
  open Setoid ⦃ … ⦄ using (_≋_)
  open Semigroupoid semigroupoid using (_∙_)
  field
    ε : ∀ {x} → 𝔐 x x
    ε-left-identity : ∀ {x y} {f : 𝔐 x y} → ε ∙ f ≋ f
    ε-right-identity : ∀ {x y} {f : 𝔐 x y} → f ∙ ε ≋ f

record Semifunctor
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔪₁} {𝔐₁ : 𝔒₁ → 𝔒₁ → Ø 𝔪₁}
  {𝔮₁} {𝔐₁-setoid : ∀ {x y} → Setoid (𝔐₁ x y) 𝔮₁}
  (semigroupoid₁ : Semigroupoid 𝔐₁ 𝔐₁-setoid)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔪₂} {𝔐₂ : 𝔒₂ → 𝔒₂ → Ø 𝔪₂}
  {𝔮₂} {𝔐₂-setoid : ∀ {x y} → Setoid (𝔐₂ x y) 𝔮₂}
  (semigroupoid₂ : Semigroupoid 𝔐₂ 𝔐₂-setoid)
  : Ø 𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂
  where
  instance _ = λ {x y} → 𝔐₁-setoid {x} {y}
  instance _ = λ {x y} → 𝔐₂-setoid {x} {y}
  open Setoid ⦃ … ⦄ using (_≋_)
  module ⒈ = Semigroupoid semigroupoid₁
  module ⒉ = Semigroupoid semigroupoid₂
  field
    {μ} : 𝔒₁ → 𝔒₂
    𝔣 : ∀ {x y} → 𝔐₁ x y → 𝔐₂ (μ x) (μ y)
    𝔣-extensionality : ∀ {x y} → {f₁ f₂ : 𝔐₁ x y} → f₁ ≋ f₂ → 𝔣 f₁ ≋ 𝔣 f₂
    𝔣-commutativity : ∀ {x y} {f : 𝔐₁ x y} {z} {g : 𝔐₁ y z} → 𝔣 (g ⒈.∙ f) ≋ 𝔣 g ⒉.∙ 𝔣 f

record Functor
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔪₁} {𝔐₁ : 𝔒₁ → 𝔒₁ → Ø 𝔪₁}
  {𝔮₁} {𝔐₁-setoid : ∀ {x y} → Setoid (𝔐₁ x y) 𝔮₁}
  {semigroupoid₁ : Semigroupoid 𝔐₁ 𝔐₁-setoid}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔪₂} {𝔐₂ : 𝔒₂ → 𝔒₂ → Ø 𝔪₂}
  {𝔮₂} {𝔐₂-setoid : ∀ {x y} → Setoid (𝔐₂ x y) 𝔮₂}
  {semigroupoid₂ : Semigroupoid 𝔐₂ 𝔐₂-setoid}
  (semifunctor : Semifunctor semigroupoid₁ semigroupoid₂)
  (category₁ : Category semigroupoid₁)
  (category₂ : Category semigroupoid₂)
  : Ø 𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂
  where
  instance _ = λ {x y} → 𝔐₂-setoid {x} {y}
  open Setoid ⦃ … ⦄ using (_≋_)
  open Semifunctor semifunctor using (𝔣; μ)
  module ⒈ = Category category₁
  module ⒉ = Category category₂
  field
    𝔣-identity : ∀ {x : 𝔒₁} → 𝔣 (⒈.ε {x = x}) ≋ (⒉.ε {x = μ x})
