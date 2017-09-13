
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Symmetry

module Oscar.Class.Symmetry.ToSym where

private

  test-class :
    ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class _∼_ ⦄
    → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class _∼_
  test-class = !

  test-class' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {x : 𝔒} {𝔯} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F (S x)) ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F (S x))
  test-class' ⦃ ⌶ ⦄ {S} = ⌶ {S} -- FIXME _S _x ≟ _S' _x

  test-class'' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {x : 𝔒} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F S x) ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F S x)
  test-class'' = !

  test-class''' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F S) ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Symmetry.class (F S)
  test-class''' = !

  test-method-sym : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : Symmetry.class _∼_ ⦄
    → _
  test-method-sym {_∼_ = _∼_} = λ {x} {y} → Symmetry.method _∼_ {x} {y}

  test-method-symmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : Symmetry.class _∼_ ⦄
    → _
  test-method-symmetry {_∼_ = _∼_} = λ {x} {y} → symmetry[ _∼_ ] {x} {y}
