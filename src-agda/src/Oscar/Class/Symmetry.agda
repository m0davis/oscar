
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Symmetry where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {x y}
  (x∼y : x ∼ y)
  where
  𝔰ymmetry : ℭlass {𝔯} $ _,_ {𝔓 = λ _∼′_ → x ∼ y} _∼_ x∼y -- FIXME "𝔓 = λ _∼′_ → x ∼ y" also works; why?; use ,, instead?; put _∼_ after x∼y?
  𝔰ymmetry = ∁ (y ∼ x)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  𝓼ymmetry = ∀ {x y} (x∼y : x ∼ y) → ℭlass.SET-METHOD (𝔰ymmetry _∼_ x∼y)
  𝓢ymmetry = ∀ {x y} {x∼y : x ∼ y} → ℭlass.GET-CLASS (𝔰ymmetry _∼_ x∼y)
  𝓢ymmetryOpen = ∀ {x y} {x∼y : x ∼ y} → ℭlass.GET-CLASS (𝔰ymmetry _∼_ x∼y)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : 𝓢ymmetry _∼_ ⦄
  where
  symmetry : {x y : 𝔒} (x∼y : x ∼ y) → y ∼ x
  symmetry {x} {y} x∼y = ℭlass.GET-METHOD (𝔰ymmetry _∼_ x∼y)
  syntax symmetry {x} {y} x∼y = x ⟨∼ x∼y ∼⟩ y

symmetry[_] : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  ⦃ _ : 𝓢ymmetry _∼_ ⦄
  → 𝓼ymmetry _∼_
symmetry[ _ ] = symmetry
