
open import Oscar.Prelude

module Oscar.Class.Symmetry where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  𝓼ymmetry = ∀ {x y} → x ∼ y → y ∼ x
  record 𝓢ymmetry : Ø 𝔬 ∙̂ 𝔯 where field symmetry : 𝓼ymmetry

  record 𝓢ymmetryOpen : Ø 𝔬 ∙̂ 𝔯 where
    field
      symmetryOpen : ∀ x y → x ∼ y → y ∼ x
    syntax symmetryOpen x y eq = x ⟨∼ eq ∼⟩ y

private

  module projection where

    open 𝓢ymmetry ⦃ … ⦄ public

    symmetry[_] : ∀
      {𝔬} {𝔒 : Ø 𝔬}
      {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
      ⦃ _ : 𝓢ymmetry _∼_ ⦄
      → 𝓼ymmetry _∼_
    symmetry[ _ ] = symmetry

open projection public

instance

  SymmetryOpenInstances : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓢ymmetryOpen _∼_
  SymmetryOpenInstances .𝓢ymmetryOpen.symmetryOpen _ _ = symmetry

open 𝓢ymmetryOpen ⦃ … ⦄ public
