
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Transitivity

module Oscar.Class.Surjtranscommutativity where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  where
  record [𝓢urjtranscommutativity] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
    ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
    where
    𝓼urjtranscommutativity = ∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → surjectivity (g ∙ f) ∼̇₂ surjectivity g ∙ surjectivity f
    record 𝓢urjtranscommutativity ⦃ _ : [𝓢urjtranscommutativity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
      field
        surjtranscommutativity : 𝓼urjtranscommutativity
      syntax surjtranscommutativity f g = g ⟪∙⟫ f

private

  module projection where

    open 𝓢urjtranscommutativity ⦃ … ⦄ public

    surjtranscommutativity[_] : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
      ⦃ _ : [𝓢urjtranscommutativity] _∼₁_ _∼₂_ _∼̇₂_ ⦄
      ⦃ _ : 𝓢urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_ ⦄
      → 𝓼urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_
    surjtranscommutativity[ _ ] = surjtranscommutativity

    ⟪∙⟫-surjtranscommutativity[]-syntax = surjtranscommutativity[_]
    syntax ⟪∙⟫-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫[ t ] f

open projection public
