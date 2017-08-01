
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical where

record 𝓢ymmetrical
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  {S : 𝔄 → 𝔄 → Ø ℓ}
  ⦃ _ : S ≡ (λ x y → (x ∼ y) ↦ (y ∼ x)) ⦄
  : Ø 𝔞 ∙̂ ℓ
  where
  field symmetrical : ∀ x y → S x y -- FIXME is there any reason to write (x ∼ y) ↦ (y ∼ x) instead of S x y?

Symmetrical : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  → Ø 𝔞 ∙̂ ℓ
Symmetrical _∼_ _↦_ = 𝓢ymmetrical _∼_ _↦_ ⦃ ∅ ⦄

symmetrical : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {_∼_ : 𝔄 → 𝔄 → 𝔅}
  {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
  ⦃ _ : Symmetrical _∼_ _↦_ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
symmetrical ⦃ I ⦄ = 𝓢ymmetrical.symmetrical I

symmetrical⟦_/_⟧ : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  ⦃ _ : Symmetrical _∼_ _↦_ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
symmetrical⟦ _ / _ ⟧ = symmetrical
