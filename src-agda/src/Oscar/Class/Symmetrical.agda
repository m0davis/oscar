
open import Oscar.Prelude

module Oscar.Class.Symmetrical where

module _
  {𝔞} (𝔄 : Ø 𝔞)
  {𝔟} (𝔅 : Ø 𝔟)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let _↦_ = _↦_ ; infix 14 _↦_)
  where

  record SymmetricalUnboxed (_∼_ : 𝔄 → 𝔄 → 𝔅) : Ø 𝔞 ∙̂ ℓ where
    field ′symmetrical : ∀ x y → x ∼ y ↦ y ∼ x

  record [𝓢ymmetrical] : Ø 𝔞 ∙̂ 𝔟 where
    constructor ∁
    infix 18 _∼_
    field
      _∼_ : 𝔄 → 𝔄 → 𝔅

  module _
    ⦃ ⌶[𝓢ymmetrical] : [𝓢ymmetrical] ⦄
    where
    record 𝓢ymmetrical : Ø 𝔞 ∙̂ ℓ where
      open [𝓢ymmetrical] ⌶[𝓢ymmetrical]
      field
        symmetrical : ∀ x y → x ∼ y ↦ y ∼ x
      instance
        ⌶SymmetricalUnboxed : SymmetricalUnboxed _∼_
        ⌶SymmetricalUnboxed .SymmetricalUnboxed.′symmetrical = symmetrical

        unboxsymmetrical : Instance (∀ x y → x ∼ y ↦ y ∼ x)
        unboxsymmetrical .Instance.x x y = symmetrical x y

  record SymmetricalContainer : Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ where
    infix 18 _∼_
    field
      _∼_ : 𝔄 → 𝔄 → 𝔅
      symmetrical′ : ∀ x y → x ∼ y ↦ y ∼ x
    -- FIXME including these instances makes instance search fussier. Perhaps because the instances in Oscar.Class.Symmetrical.Symmetry should make `SymmetricalContainer`s?
    -- instance
    --   ⌶[𝓢ymmetrical] : [𝓢ymmetrical]
    --   ⌶[𝓢ymmetrical] = ∁ _∼_
    --   ⌶𝓢ymmetrical : 𝓢ymmetrical
    --   ⌶𝓢ymmetrical .𝓢ymmetrical.symmetrical = symmetrical′

open import Oscar.Data.Proposequality

open 𝓢ymmetrical ⦃ … ⦄ public

open SymmetricalUnboxed ⦃ … ⦄ public

open Instance ⦃ … ⦄ renaming (x to ti) public

getSymmetricalContainerInstance : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  ⦃ _ : Σ (SymmetricalContainer 𝔄 𝔅 _↦_) λ SC → SymmetricalContainer._∼_ SC ≡ _∼_ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
getSymmetricalContainerInstance _∼_ ⦃ SC , ∅ ⦄ = SymmetricalContainer.symmetrical′ SC

explicit-symmetrical : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  -- ⦃ _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_ ⦄
  ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦃ ∁ _∼_ ⦄ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
explicit-symmetrical _↦_ _∼_ ⦃ I ⦄ x₁ y = symmetrical ⦃ r = I ⦄ x₁ y
