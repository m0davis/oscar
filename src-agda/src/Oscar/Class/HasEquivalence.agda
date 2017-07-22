
open import Oscar.Prelude
open import Oscar.Class.IsEquivalence

module Oscar.Class.HasEquivalence where

module _ where

  record HasEquivalence {𝔬} (𝔒 : Ø 𝔬) ℓ : Ø 𝔬 ∙̂ ↑̂ ℓ where
    constructor ∁

    field
      Equivalence : 𝔒 → 𝔒 → Ø ℓ
      ⦃ ⌶IsEquivalence ⦄ : IsEquivalence Equivalence
    infix 4 Equivalence

  open HasEquivalence ⦃ … ⦄ public
  open HasEquivalence ⦃ … ⦄ public using () renaming (Equivalence to _≈_)

  module _ where

    infix 4 ≈-syntax
    ≈-syntax : ∀ {𝔬} (𝔒 : Ø 𝔬) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    ≈-syntax _ = _≈_
    syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y
