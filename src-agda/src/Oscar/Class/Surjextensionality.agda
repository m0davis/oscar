
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Data.Constraint

module Oscar.Class.Surjextensionality where

private

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
    where
    module TypeConstructorVisible
      (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
      (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
      where
      module FunctionVisible
        (surjection : 𝓼urjection 𝔒₁ 𝔒₂)
        (surjectivity : 𝓈urjectivity _∼₁_ _∼₂_ surjection)
        where
        𝓼urjextensionality′ = λ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂
        𝓈urjextensionality′ = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂
        Surjextensionality : Ø _
        Surjextensionality = ∀ {x y} → Surjectivity (_∼̇₁_ {x} {y}) _∼̇₂_ surjectivity
      module FunctionInstance
        ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
        ⦃ _ : Surjectivity _∼₁_ _∼₂_ surjection ⦄
        where
        open FunctionVisible surjection surjectivity
        𝓼urjextensionality = 𝓈urjextensionality′
        𝓈urjextensionality = 𝓼urjextensionality′
        𝓢urjextensionality = Surjextensionality

open TypeConstructorVisible.FunctionVisible public
open TypeConstructorVisible.FunctionInstance public

private

  module projection where

    surjextensionality = surjectivity

    surjextensionality[_] : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : Surjectivity _∼₁_ _∼₂_ surjection ⦄
      ⦃ _ : 𝓢urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
      → 𝓼urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
    surjextensionality[ _ ] = surjextensionality

open projection public

module _ where
  open projection public using () renaming (surjextensionality to ⟪_⟫)
  ⟪⟫-surjextensionality[]-syntax = surjextensionality[_]
  syntax ⟪⟫-surjextensionality[]-syntax t x = ⟪ x ⟫[ t ]
