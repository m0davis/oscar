
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Symmetry where

module SymmetryClass
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y}
  (x∼y : x ∼ y)
  where
  𝔰ymmetry : ℭlass {𝔯} $ _∼_ ,, x∼y
  𝔰ymmetry = ∁ $′ y ∼ x

module SymmetryInterface0
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y}
  (x∼y : x ∼ y)
  where
  open ℭlass (SymmetryClass.𝔰ymmetry _∼_ x∼y) public

module SymmetryInterface1
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  open SymmetryInterface0 _∼_
  𝓢ymmetry = ∀ {x y} {x∼y : x ∼ y} → GET-CLASS x∼y

module SymmetryInterface2
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  open SymmetryInterface1 _∼_
  open SymmetryInterface0 _∼_
  𝓼ymmetry = ∀ {x y} (x∼y : x ∼ y) → SET-METHOD x∼y
  module _
    ⦃ _ : 𝓢ymmetry ⦄
    where
    symmetry[_] = 𝓼ymmetry ∋ λ {x} {y} (x∼y : x ∼ y) → GET-METHOD x∼y

module SymmetryInterface3
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  open SymmetryInterface2 _∼_
  symmetry = symmetry[_]
  syntax symmetry {x} {y} x∼y = x ⟨∼ x∼y ∼⟩ y

open SymmetryClass public
open SymmetryInterface1 public
open SymmetryInterface2 public
open SymmetryInterface3 public
