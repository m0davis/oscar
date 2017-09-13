
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Symmetry

module Oscar.Class.Symmetry.ToSym where

instance

  SymFrom𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → Sym.⟦ _∼_ ⟧
  SymFrom𝓢ymmetry .⋆ = symmetry

private

  test-class :
    ⦃ _ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ _∼_ ⟧ ⦄
    → ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ _∼_ ⟧
  test-class = !

  test-class' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {x : 𝔒} {𝔯} {F : (𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F (S x) ⟧ ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F (S x) ⟧
  test-class' ⦃ ⌶ ⦄ {S} = ⌶ {S} -- FIXME _S _x ≟ _S' _x

  test-class'' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {x : 𝔒} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F S x ⟧ ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F S x ⟧
  test-class'' = !

  test-class''' :
    ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {F : (𝔒 → 𝔒 → 𝔒 → Ø 𝔯) → 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F S ⟧ ⦄
    → ∀ {S : 𝔒 → 𝔒 → 𝔒 → Ø 𝔯} → Sym.⟦ F S ⟧
  test-class''' = !

  test-method-sym : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → _
  test-method-sym {_∼_ = _∼_} = λ {x} {y} → Sym.[ _∼_ ] {x} {y}

  test-method-symmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → _
  test-method-symmetry {_∼_ = _∼_} = λ {x} {y} → symmetry[ _∼_ ] {x} {y}
