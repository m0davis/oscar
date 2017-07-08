{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude

module _ where

  record HasEquivalence {𝔬} (𝔒 : Ø 𝔬) ℓ : Ø 𝔬 ∙̂ ↑̂ ℓ where
    constructor ∁

    field
      Equivalence : 𝔒 → 𝔒 → Ø ℓ

  open HasEquivalence ⦃ … ⦄ public

  module _ where

    infix 4 _≈_
    _≈_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    _≈_ = HasEquivalence.Equivalence !

    infix 4 ≈-syntax
    ≈-syntax : ∀ {𝔬} (𝔒 : Ø 𝔬) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    ≈-syntax _ = _≈_
    syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y

module _ where

  record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
    field
      ➊ : 𝔒
      _∧_ : 𝔒 → 𝔒 → 𝔒

  open Properthing ⦃ … ⦄ public
