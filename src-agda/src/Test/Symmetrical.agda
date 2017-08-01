
open import Oscar.Prelude
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
import Oscar.Class.Symmetrical.Symmetry
import Oscar.Data.Proposequality

module Test.Symmetrical where

  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  -- test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _ -- FIXME no longer works after 𝓢ymmetrical𝓢ymmetry was "rationalised"
  test-𝓢ymmetrical𝓢ymmetry {𝔒 = 𝔒} = symmetrical {𝔄 = 𝔒} _ _

  test-𝓢ymmetrical𝓢ymmetry-alternate : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry-alternate {x = x} = symmetrical x _

  lhs-test1 : ∀ {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    {_∼'_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼'_ ⦄
    → ∀ x y → _
  lhs-test1 {_∼_ = _∼_} = explicit-symmetrical _∼_ (λ x y → x → y)

  module OverlappingInstances
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
        {_↦'_ : 𝔅 → 𝔅 → Ø ℓ}
    {_∼1_ : 𝔄 → 𝔄 → 𝔅}
    {_∼2_ : 𝔄 → 𝔄 → 𝔅}
    ⦃ _ : [𝓢ymmetrical] _∼1_ _↦_ ⦄
    ⦃ _ : 𝓢ymmetrical _∼1_ _↦_ ⦄
    ⦃ _ : [𝓢ymmetrical] _∼1_ _↦'_ ⦄
    ⦃ _ : 𝓢ymmetrical _∼1_ _↦'_ ⦄
    ⦃ _ : [𝓢ymmetrical] _∼2_ _↦_ ⦄
    ⦃ _ : 𝓢ymmetrical _∼2_ _↦_ ⦄
    ⦃ _ : [𝓢ymmetrical] _∼2_ _↦'_ ⦄
    ⦃ _ : 𝓢ymmetrical _∼2_ _↦'_ ⦄
    (x y : 𝔄)
    where

    test1 = symmetrical {Symmetrical = λ x y → (x ∼1 y) ↦ (y ∼1 x)} x y

    test2 : (x ∼1 y) ↦ (y ∼1 x)
    test2 = explicit-symmetrical _ _↦_ x y

    test2a : (x ∼1 y) ↦ (y ∼1 x)
    test2a = symmetrical x y

    test3 = explicit-symmetrical _∼1_ _↦_ x y

  lhs-test2a : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    (_∼_ : 𝔄 → 𝔄 → 𝔅)
    {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
    ⦃ _ : [𝓢ymmetrical] _∼_ _↦_ ⦄
    ⦃ _ : 𝓢ymmetrical _∼_ _↦_ ⦄
    → ∀ (x y : 𝔄) → _ ↦ _
  lhs-test2a _∼_ _↦_ x y =
    -- symmetrical x y -- works
    explicit-symmetrical _∼_ _↦_ x y -- works
    -- explicit-symmetrical _ _↦_ x y -- FIXME fails; explain why
    -- explicit-symmetrical _∼_ _ x y -- FIXME fails; explain why
