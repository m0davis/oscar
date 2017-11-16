
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
import Oscar.Data.Constraint

module Oscar.Class.Properthing where

record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
  infixr 15 _∧_
  field
    ➊ : 𝔒
    _∧_ : 𝔒 → 𝔒 → 𝔒
    ⦃ ⌶HasEquivalence ⦄ : HasEquivalence 𝔒 ℓ
    Nothing : 𝔒 → Ø ℓ
    fact2 : ∀ {P Q} → P ≈ Q → Nothing P → Nothing Q
    ∧-leftIdentity : ∀ P → ➊ ∧ P ≈ P

open Properthing ⦃ … ⦄ public
