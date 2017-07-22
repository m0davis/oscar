
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity

module Oscar.Class.Surjextensionality where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  where
  record [𝓢urjextensionality] : Ø 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    where
    𝓼urjextensionality = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂
    record 𝓢urjextensionality ⦃ _ : [𝓢urjextensionality] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where field surjextensionality : 𝓼urjextensionality

private

  module projection where

    open 𝓢urjextensionality ⦃ … ⦄ public

    surjextensionality[_] : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      ⦃ _ : [𝓢urjextensionality] _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
      ⦃ _ : 𝓢urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
      → 𝓼urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
    surjextensionality[ _ ] = surjextensionality

open projection public

module _ where
  open projection public using () renaming (surjextensionality to ⟪_⟫)
  ⟪⟫-surjextensionality[]-syntax = surjextensionality[_]
  syntax ⟪⟫-surjextensionality[]-syntax t x = ⟪ x ⟫[ t ]
