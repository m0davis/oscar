
open import Oscar.Prelude
open import Oscar.Class.Smap
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjection
open import Oscar.Class.Surjidentity

module Test.SurjidentityI where

module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
         (_∼₂2_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {𝔯₂'} (_∼₂'_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂')
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
         (_∼̇₂'_ : ∀ {x y} → x ∼₂' y → x ∼₂' y → Ø ℓ₂)
         (_∼̇₂2_ : ∀ {x y} → x ∼₂2 y → x ∼₂2 y → Ø ℓ₂)
  where
  postulate
    instance `𝓢urjection : Surjection.class 𝔒₁ 𝔒₂
    instance `𝓢urjectivity : Smap!.class _∼₁_ _∼₂_
    instance `𝓢urjectextensivity : Smap!.class _∼₁_ _∼₂'_
    instance `𝓢urjectivity2 : Smap!.class _∼₁_ _∼₂2_
    instance `𝓡eflexivity₁ : 𝓡eflexivity _∼₁_
    instance `𝓡eflexivity₂ : 𝓡eflexivity _∼₂_
    instance `𝓡eflexivity₂' : 𝓡eflexivity _∼₂'_
    instance `𝓡eflexivity₂2 : 𝓡eflexivity _∼₂2_
    instance `𝒮urjidentity : Surjidentity!.class _∼₁_ _∼₂_ _∼̇₂_
    instance `𝒮urjidentity' : Surjidentity!.class _∼₁_ _∼₂'_ _∼̇₂'_
    instance `𝒮urjidentity2 : Surjidentity!.class _∼₁_ _∼₂2_ _∼̇₂2_

  test-surj : Surjidentity!.type _∼₁_ _∼₂_ _∼̇₂_
  test-surj = surjidentity
