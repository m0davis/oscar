
module Oscar.Category.Semigroupoid where

open import Oscar.Category.Morphism
open import Oscar.Category.Setoid
open import Oscar.Level

module _
  {𝔬} {⋆ : Set 𝔬}
  {𝔪} {𝔮} (𝔐 : Morphism ⋆ 𝔪 𝔮)
  where

  open Morphism 𝔐

  record IsSemigroupoid
    (_∙_ : ∀ {y z} → y ↦ z → ∀ {x} → x ↦ y → x ↦ z)
    : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮))
    where
    instance _ = IsSetoid↦

    field
      extensionality :
        ∀ {x y} {f₁ f₂ : x ↦ y} →
        f₁ ≋ f₂ →
        ∀ {z} {g₁ g₂ : y ↦ z} →
        g₁ ≋ g₂ →
        g₁ ∙ f₁ ≋ g₂ ∙ f₂

    field
      associativity :
        ∀ {w x}
        (f : w ↦ x)
        {y}
        (g : x ↦ y)
        {z}
        (h : y ↦ z)
        → ((h ∙ g) ∙ f) ≋ (h ∙ (g ∙ f))

open IsSemigroupoid ⦃ … ⦄ public

infixr 4 _,_
record Semigroupoid 𝔬 𝔪 𝔮
       : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮))
  where
  constructor _,_

  field
    {⋆} : Set 𝔬
    𝔐 : Morphism ⋆ 𝔪 𝔮
  open Morphism 𝔐 public

  infixl 7 _∙_
  field _∙_ : ∀ {y z} → y ↦ z → ∀ {x} → x ↦ y → x ↦ z

  field ⦃ isSemigroupoid ⦄ : IsSemigroupoid 𝔐 _∙_
  open IsSemigroupoid isSemigroupoid public
