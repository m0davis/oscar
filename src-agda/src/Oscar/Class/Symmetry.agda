
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Symmetry where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y}
  (x∼y : x ∼ y)
  where
  𝔰ymmetry : ℭlass {𝔯} $ _∼_ ,, x∼y
  𝔰ymmetry = ∁ $′ y ∼ x

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private
    module _
      {x y}
      (x∼y : x ∼ y)
      where
      open ℭlass (𝔰ymmetry _∼_ x∼y) public
  𝓢ymmetry = ∀ {x y} {x∼y : x ∼ y} → GET-CLASS x∼y
  𝓼ymmetry = ∀ {x y} (x∼y : x ∼ y) → SET-METHOD x∼y
  symmetry[_] = λ ⦃ _ : 𝓢ymmetry ⦄ {x} {y} (x∼y : x ∼ y) → GET-METHOD x∼y

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  symmetry = symmetry[ _∼_ ]
  syntax symmetry {x} {y} x∼y = x ⟨∼ x∼y ∼⟩ y
