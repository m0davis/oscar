
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Symmetry where

module Symmetry'
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  x y
  = ℭLASS (x ,, y ,, _∼_) (x ∼ y → y ∼ x)

module Symmetry
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  class = ∀ {x y} → Symmetry'.class _∼_ x y
  type = ∀ {x y} → Symmetry'.type _∼_ x y
  method : ⦃ _ : class ⦄ → type
  method {x = x} {y} = Symmetry'.method _∼_ x y

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  symmetry = Symmetry.method _∼_
  syntax symmetry {x} {y} x∼y = x ⟨∼ x∼y ∼⟩ y

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  ⦃ _ : Symmetry.class _∼_ ⦄
  where
  symmetry[_] = λ {x y} (x∼y : x ∼ y) → Symmetry.method _∼_ x∼y
