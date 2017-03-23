
module Oscar.Category.Category where

open import Oscar.Category.Setoid
open import Oscar.Category.Semigroupoid
open import Oscar.Level

module _
  {𝔬 𝔪 𝔮}
  (semigroupoid : Semigroupoid 𝔬 𝔪 𝔮)
  where
  open Semigroupoid semigroupoid

  record IsCategory (ε : ∀ {x} → x ↦ x) : Set (𝔬 ⊔ 𝔪 ⊔ 𝔮) where
    instance _ = IsSetoid↦
    field
      left-identity : ∀ {x y} (f : x ↦ y) → ε ∙ f ≋ f
      right-identity : ∀ {x y} (f : x ↦ y) → f ∙ ε ≋ f

open IsCategory ⦃ … ⦄ public

record Category 𝔬 𝔪 𝔮 : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮)) where
  constructor _,_
  field
    semigroupoid : Semigroupoid 𝔬 𝔪 𝔮
  open Semigroupoid semigroupoid public

  field
    ε : ∀ {x} → x ↦ x
    ⦃ isCategory ⦄ : IsCategory semigroupoid ε
  open IsCategory isCategory public
