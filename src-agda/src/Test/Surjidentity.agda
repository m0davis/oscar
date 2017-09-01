
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjidentity
open import Oscar.Data.Proposequality -- FIXME I'm surprised that this import is needed to avoid the following error:
{-
No instance of type
.Oscar.Data.Proposequality
(λ x →
   𝓢urjectivity.surjectivity `𝓢urjectivity
   (𝓡eflexivity.reflexivity `𝓡eflexivity₁)
   ∼̇₂ 𝓡eflexivity.reflexivity `𝓡eflexivity₂)
(λ x →
   𝓢urjectivity.surjectivity `𝓢urjectivity
   (𝓡eflexivity.reflexivity `𝓡eflexivity₁)
   ∼̇₂ 𝓡eflexivity.reflexivity `𝓡eflexivity₂)
was found in scope.
-}

module Test.Surjidentity where

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔒₂ : Ø 𝔬₂}
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼₂'_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  (_∼̇₂'_ : ∀ {x y} → x ∼₂' y → x ∼₂' y → Ø ℓ₂)
  ⦃ `𝓢urjection : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ `𝓢urjectivity : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ `𝓢urjectextensivity : Smap!.class _∼₁_ _∼₂'_ ⦄
  ⦃ `𝓡eflexivity₁ : 𝓡eflexivity _∼₁_ ⦄
  ⦃ `𝓡eflexivity₂ : 𝓡eflexivity _∼₂_ ⦄
  ⦃ `𝓡eflexivity₂' : 𝓡eflexivity _∼₂'_ ⦄
  where
  instance

    `𝒮urjidentity : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_
    `𝒮urjidentity .⋆ = magic

  test-surjidentity : 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-surjidentity = surjidentity
