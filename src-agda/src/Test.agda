-- a hodge-podge of tests

module Test where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
import Test.Transassociativity
import Test.Surjidentity
import Test.SurjidentityI
import Test.SurjidentityP
import Test.Test0
import Test.Test1

module Test2 where

  test-functor-transextensionality : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    → 𝓽ransextensionality _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality

module Test3 (_ : Ø₀) where

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    where
    postulate instance functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂
    open Functor ⦃ … ⦄
    test : asInstance `IsFunctor $ 𝓽ransextensionality _∼₁_ _∼̇₁_
    test = asInstance `IsFunctor transextensionality
    -- -- Test1.test-functor-transextensionality

module Test4
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ : Ł}
  ⦃ _ : 𝓣ransitivity (Arrow 𝔒₁ 𝔒₂) ⦄
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowṖroperty ℓ 𝔒₁ 𝔒₂) ⦄
  where
  test[∙] : ∀ {x y} → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ y
  test[∙] P f .π₀ g = (f ◃ P) .π₀ g


module Test5
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
  ⦃ _ : [ExtensibleType] _↦_ ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : [𝓢urjextensionality] (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
  ⦃ _ : 𝓢urjextensionality (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_) ⦄
  where
  test[∙] : ∀ {x y} → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ y
  test[∙] P f = f ◃ P

module Test7 where

  𝓅rop-id : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    {m n}
    {ℓ} {f : m ∼ n} (P : ExtensionṖroperty ℓ (Arrow 𝔄 𝔅 m) _∼̇_) (let P₀ = π₀ (π₀ P))
    → P₀ f
    → P₀ (ε ∙ f)
  𝓅rop-id = prop-id

module TestEquivalenceṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  test-sym-regular : {P Q : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ P
  test-sym-regular = symmetry

  test-trans-regular : {P Q R : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-regular P≈Q Q≈R = transitivity P≈Q Q≈R

module TestEquivalenceExtensionṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  test-sym-ext : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext P≈Q = symmetry P≈Q

  test-trans-ext : {P Q R : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-ext P≈Q Q≈R = transitivity P≈Q Q≈R

module TestSymmetrical where
  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _
