
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Reflexivity
open import Oscar.Data.Proposequality

module Oscar.Class.Surjidentity where

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔒₂ : Ø 𝔬₂}
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
  where
  [𝓈urjidentity] : π̂ ℓ₂ 𝔒₁
  [𝓈urjidentity] x = surjectivity (ε[ _∼₁_ ] {x}) ∼̇₂ ε

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁} {ℓ₂} (𝔓 : π̂ ℓ₂ 𝔒₁)
  where
  𝓈urjidentity = ∀ {x} → 𝔓 x
  module _
    𝔯₁ 𝔬₂ 𝔯₂
    where
    record [𝒮urjidentity] : Ø 𝔬₁ ∙̂ ↑̂ (𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
      constructor ∁
      field
        _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
        {𝔒₂} : Ø 𝔬₂
        _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
        _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
        ⦃ `𝓢urjection     ⦄ : 𝓢urjection 𝔒₁ 𝔒₂
        ⦃ `[𝓢urjectivity] ⦄ : [𝓢urjectivity] _∼₁_ _∼₂_
        ⦃ `𝓢urjectivity   ⦄ : 𝓢urjectivity _∼₁_ _∼₂_
        ⦃ `𝓡eflexivity₁   ⦄ : 𝓡eflexivity _∼₁_
        ⦃ `𝓡eflexivity₂   ⦄ : 𝓡eflexivity _∼₂_
        ⦃ `Proposequality[𝓈urjidentity] ⦄ : [𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_ ≡ 𝔓
  module _
    {𝔯₁ 𝔬₂ 𝔯₂}
    ⦃ _ : [𝒮urjidentity] 𝔯₁ 𝔬₂ 𝔯₂ ⦄
    where
    record 𝒮urjidentity : Ø 𝔬₁ ∙̂ ℓ₂ where
      field surjidentity : 𝓈urjidentity

open 𝒮urjidentity ⦃ … ⦄ public

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔒₂ : Ø 𝔬₂}
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
  where
  𝓼urjidentity = 𝓈urjidentity ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_)
  [𝓢urjidentity] = [𝒮urjidentity] ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_) 𝔯₁ 𝔬₂ 𝔯₂
  𝓢urjidentity = 𝒮urjidentity ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_) {𝔯₁} {𝔬₂} {𝔯₂}

surjidentity[_,_] : ∀
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔒₂ : Ø 𝔬₂}
  {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
  ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
  ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ ⦄
  ⦃ _ : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_ ⦄
  → 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
surjidentity[ _ , _ ] = surjidentity
