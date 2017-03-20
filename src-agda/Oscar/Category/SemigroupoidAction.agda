
module Oscar.Category.SemigroupoidAction where

open import Oscar.Category.Action
open import Oscar.Category.Setoid
open import Oscar.Category.Semigroupoid
open import Oscar.Function
open import Oscar.Level

module _ {𝔊𝔬 𝔊𝔪 𝔊𝔮} (semigroupoid : Semigroupoid 𝔊𝔬 𝔊𝔪 𝔊𝔮) where
  open Semigroupoid semigroupoid

  module _ {𝔄𝔬 𝔄𝔮} (action : Action ⋆ 𝔄𝔬 𝔄𝔮) where
    open Action action

    record IsSemigroupoidAction
      (_◂_ : ∀ {x y} → x ↦ y → ↥ x → ↥ y)
      : Set (𝔊𝔬 ⊔ 𝔊𝔪 ⊔ 𝔊𝔮 ⊔ 𝔄𝔬 ⊔ 𝔄𝔮)
      where
      field
        extensionality :
          ∀ {x} {s₁ s₂ : ↥ x} →
          s₁ ≋ s₂ →
          ∀ {y} {f₁ f₂ : x ↦ y} →
          f₁ ≋ f₂ → f₁ ◂ s₁ ≋ f₂ ◂ s₂
        associativity :
          ∀ {x}
          (s : ↥ x)
          {y}
          (f : x ↦ y)
          {z}
          (g : y ↦ z) →
          (g ∙ f) ◂ s ≋ g ◂ (f ◂ s)

open IsSemigroupoidAction ⦃ … ⦄ public

record SemigroupoidAction 𝔊𝔬 𝔊𝔪 𝔊𝔮 𝔄𝔬 𝔄𝔮 : Set (lsuc (𝔊𝔬 ⊔ 𝔊𝔪 ⊔ 𝔊𝔮 ⊔ 𝔄𝔬 ⊔ 𝔄𝔮)) where
  constructor [_/_]
  field
    semigroupoid : Semigroupoid 𝔊𝔬 𝔊𝔪 𝔊𝔮
  open Semigroupoid semigroupoid public

  field
    action : Action ⋆ 𝔄𝔬 𝔄𝔮
  open Action action public

  field
    _◂_ : ∀ {x y} → x ↦ y → ↥ x → ↥ y
    ⦃ isSemigroupoidAction ⦄ : IsSemigroupoidAction semigroupoid action _◂_
