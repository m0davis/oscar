
open import Oscar.Prelude
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjtranscommutativity
open import Oscar.Class.Surjextensionality

module Oscar.Class.IsPrefunctor where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  where
  record IsPrefunctor : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
    constructor ∁
    field
      overlap ⦃ `IsPrecategory₁ ⦄ : IsPrecategory _∼₁_ _∼̇₁_
      overlap ⦃ `IsPrecategory₂ ⦄ : IsPrecategory _∼₂_ _∼̇₂_
      overlap ⦃ `𝓢urjection ⦄ : Surjection.class 𝔒₁ 𝔒₂
      overlap ⦃ `𝓢urjectivity ⦄ : 𝒮urjectivity! _∼₁_ _∼₂_
      overlap ⦃ `𝓢urjtranscommutativity ⦄ : 𝓢urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_
      ⦃ `𝓢urjextensionality ⦄ : 𝓢urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
