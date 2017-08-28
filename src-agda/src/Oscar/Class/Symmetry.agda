
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Symmetry where

module SymmetryClass
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y}
  (x∼y : x ∼ y)
  = ℭLASS (_∼_ ,, x∼y) (y ∼ x)

module SymmetryInterface0
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (∼ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y : 𝔒}
  (x∼y : ∼ x y)
  = SymmetryClass ∼ x∼y

module SymmetryInterface1
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  open SymmetryInterface0 _∼_
  𝓢ymmetry = ∀ {x y} {x∼y : x ∼ y} → class x∼y

module SymmetryInterface2
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  open SymmetryInterface1 _∼_
  open SymmetryInterface0 _∼_
  𝓼ymmetry = ∀ {x y} (x∼y : x ∼ y) → type x∼y
  module _
    ⦃ _ : 𝓢ymmetry ⦄
    where
    symmetry[_] = 𝓼ymmetry ∋ λ {x} {y} (x∼y : x ∼ y) → method x∼y

module SymmetryInterface3
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  open SymmetryInterface2 _∼_
  symmetry = symmetry[_]
  syntax symmetry {x} {y} x∼y = x ⟨∼ x∼y ∼⟩ y

open SymmetryInterface1 public
open SymmetryInterface2 public
open SymmetryInterface3 public

module Sym
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯}
  where
  module _
    (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    private module M x y = ℭLASS (_∼_ ,, x ,, y) (x ∼ y → y ∼ x)
    ⟦_⟧ = ∀ {x y} → M.class x y
    ⟨_⟩ = ∀ {x y} → M.type x y
    [_] : ⦃ _ : ⟦_⟧ ⦄ → ⟨_⟩
    [_] = M.method _ _
  module _
    {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    where
    private module M x y = ℭLASS (_∼_ ,, x ,, y) (x ∼ y → y ∼ x)
    [] : ⦃ _ : ⟦ _∼_ ⟧ ⦄ → ⟨ _∼_ ⟩
    [] = M.method _ _

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
