
module Oscar.Category.Semigroup where

open import Oscar.Category.Setoid
open import Oscar.Level

module _ {𝔬 𝔮} (setoid : Setoid 𝔬 𝔮) where
  open Setoid setoid

  record IsSemigroup (_∙_ : ⋆ → ⋆ → ⋆) : Set (𝔬 ⊔ 𝔮) where
    field
      extensionality : ∀ {f₁ f₂} → f₁ ≋ f₂ → ∀ {g₁ g₂} → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
      associativity : ∀ f g h → (h ∙ g) ∙ f ≋ h ∙ (g ∙ f)

open IsSemigroup ⦃ … ⦄ public

record Semigroup 𝔬 𝔮 : Set (lsuc (𝔬 ⊔ 𝔮)) where
  field
    setoid : Setoid 𝔬 𝔮
  open Setoid setoid public

  infixl 7 _∙_
  field
    _∙_ : ⋆ → ⋆ → ⋆
    ⦃ isSemigroup ⦄ : IsSemigroup setoid _∙_
