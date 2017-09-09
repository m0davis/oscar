
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
   𝓢urjectivity.smap `𝓢urjectivity
   (𝓡eflexivity.reflexivity `𝓡eflexivity₁)
   ∼̇₂ 𝓡eflexivity.reflexivity `𝓡eflexivity₂)
(λ x →
   𝓢urjectivity.smap `𝓢urjectivity
   (𝓡eflexivity.reflexivity `𝓡eflexivity₁)
   ∼̇₂ 𝓡eflexivity.reflexivity `𝓡eflexivity₂)
was found in scope.
-}
open import Oscar.Class.Transitivity
open import Oscar.Class.IsFunctor

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
  (_↦₁_ : Transitivity.type _∼₁_)
  (_↦₂_ : Transitivity.type _∼₂_)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  {ℓ₁'} (_∼̇₁'_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁')
  (μ₁₂ : Surjection.type _ _)
  (μ₂₂ : Surjection.type _ _)
  {smap₁₂ : Smap.type _∼₁_ _∼₂_ μ₁₂ μ₁₂}
  {smap₂₂ : Smap.type _∼₂_ _∼₂_ μ₂₂ μ₂₂}
  ⦃ I1 : IsFunctor _∼₁_ _∼̇₁_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂ ⦄ -- FIXME using top-level instances does not work b/c then there is not instance found for reflexivity.
  ⦃ I2 : IsFunctor _∼₂_ _∼̇₂_ _↦₂_ _∼₂_ _∼̇₂_ _↦₂_ smap₂₂ ⦄
  ⦃ I3 : IsFunctor _∼₁_ _∼̇₁'_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂ ⦄
  where
  {- FIXME would like to try this instead of instance arguments
  postulate
    instance
      I1 : IsFunctor _∼₁_ _∼̇₁_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂
      I2 : IsFunctor _∼₂_ _∼̇₂_ _↦₂_ _∼₂_ _∼̇₂_ _↦₂_ smap₂₂
      I3 : IsFunctor _∼₁_ _∼̇₁'_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂
  -}

  test-surjidentity-from-IsFunctor : Surjidentity.type _∼₁_ _∼₂_ _∼̇₂_ smap₁₂ ε ε
  test-surjidentity-from-IsFunctor = surjidentity -- FIXME this works only b/c of overlap (the Surjidentity instance found is I1, not I3)

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
  ⦃ `𝓡eflexivity₁ : Reflexivity.class _∼₁_ ⦄
  ⦃ `𝓡eflexivity₂ : Reflexivity.class _∼₂_ ⦄
  ⦃ `𝓡eflexivity₂' : Reflexivity.class _∼₂'_ ⦄
  where

  instance

    `𝒮urjidentity : Surjidentity!.class _∼₁_ _∼₂_ _∼̇₂_
    `𝒮urjidentity .⋆ = magic

  test-surjidentity : Surjidentity!.type _∼₁_ _∼₂_ _∼̇₂_
  test-surjidentity = surjidentity

module _

  where
