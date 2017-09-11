
open import Everything

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
  (ε₁ : Reflexivity.type _∼₁_)
  (ε₂ : Reflexivity.type _∼₂_)
  (_↦₁_ : Transitivity.type _∼₁_)
  (_↦₂_ : Transitivity.type _∼₂_)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  {ℓ₁'} (_∼̇₁'_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁')
  (μ₁₂ : Surjection.type _ _)
  (μ₂₂ : Surjection.type _ _)
  {smap₁₂ : Smap.type _∼₁_ _∼₂_ μ₁₂ μ₁₂}
  {smap₂₂ : Smap.type _∼₂_ _∼₂_ μ₂₂ μ₂₂}
  ⦃ I1 : IsFunctor _∼₁_ _∼̇₁_ ε₁ _↦₁_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ smap₁₂ ⦄ -- FIXME using top-level instances does not work b/c then there is not instance found for reflexivity.
  ⦃ I2 : IsFunctor _∼₂_ _∼̇₂_ ε₂ _↦₂_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ smap₂₂ ⦄
  ⦃ I3 : IsFunctor _∼₁_ _∼̇₁'_ ε₁ _↦₁_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ smap₁₂ ⦄
  where
  {- FIXME would like to try this instead of instance arguments
  postulate
    instance
      I1 : IsFunctor _∼₁_ _∼̇₁_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂
      I2 : IsFunctor _∼₂_ _∼̇₂_ _↦₂_ _∼₂_ _∼̇₂_ _↦₂_ smap₂₂
      I3 : IsFunctor _∼₁_ _∼̇₁'_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap₁₂
  -}

  test-surjidentity-from-IsFunctor : Surjidentity.type _∼₁_ _∼₂_ _∼̇₂_ smap₁₂ ε₁ ε₂
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
