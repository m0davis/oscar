
module Oscar.Category.Action where

open import Oscar.Category.Setoid
open import Oscar.Function
open import Oscar.Level

record Action {𝔬} (⋆ : Set 𝔬) 𝔄𝔬 𝔄𝔮
       : Set (𝔬 ⊔ lsuc (𝔄𝔬 ⊔ 𝔄𝔮))
  where

  field
    𝔄 : ⋆ → Setoid 𝔄𝔬 𝔄𝔮
    ⦃ isSetoid ⦄ : ∀ {x} → IsSetoid (Setoid.⋆ (𝔄 x)) 𝔄𝔮

  ↥ : ⋆ → Set 𝔄𝔬
  ↥ = Setoid.⋆ ∘ 𝔄
