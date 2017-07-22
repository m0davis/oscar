
open import Oscar.Prelude
open import Oscar.Class.Properthing
open import Oscar.Class.HasEquivalence
open import Oscar.Data

module Oscar.Class.Properfact1 where

Refl4 : ∀ {𝔞} ℓ → Ø 𝔞 → Ø 𝔞 ∙̂ ↑̂ ℓ
Refl4 ℓ 𝔄 = 𝔄 → 𝔄 → 𝔄 → 𝔄 → Ø ℓ

𝓅roperfact1 : ∀ {𝔞} {𝔄 : Ø 𝔞} {ℓ} → Refl4 ℓ 𝔄 → Ø 𝔞 ∙̂ ℓ
𝓅roperfact1 refl4 = ∀ s1 s2 t1 t2 → refl4 s1 s2 t1 t2

[𝓹roperfact1] : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_∼_ : 𝔄 → 𝔄 → 𝔅) (_⊛_ : 𝔄 → 𝔄 → 𝔄) → Refl4 ℓ 𝔄
[𝓹roperfact1] _∼_ _⊛_ s1 s2 t1 t2 = let _∼_ = _∼_ ; infix 18 _∼_ in
  s1 ⊛ s2 ∼ t1 ⊛ t2 ≈ s1 ∼ t1 ∧ s2 ∼ t2

module _
  {𝔞} {𝔄 : Ø 𝔞} ℓ (refl4 : Refl4 ℓ 𝔄)
  where
  record [𝒫roperfact1] 𝔟 : Ø 𝔞 ∙̂ ↑̂ 𝔟 ∙̂ ↑̂ ℓ where
    constructor ∁
    infix 18 _∼_
    field
      𝔅 : Ø 𝔟
      _∼_ : 𝔄 → 𝔄 → 𝔅
      ⦃ ⌶Properthing ⦄ : Properthing ℓ 𝔅
      _⊛_ : 𝔄 → 𝔄 → 𝔄
      ⦃ ⌶CorrectProp ⦄ : [𝓹roperfact1] _∼_ _⊛_ ≡ refl4

  record 𝒫roperfact1 {𝔟} ⦃ _ : [𝒫roperfact1] 𝔟 ⦄ : Ø 𝔞 ∙̂ ℓ where
    field properfact1 : 𝓅roperfact1 refl4

open 𝒫roperfact1 ⦃ … ⦄ public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} (_∼_ : 𝔄 → 𝔄 → 𝔅) {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  𝓹roperfact1 = 𝓅roperfact1 ([𝓹roperfact1] _∼_ _⊛_)
  [𝓟roperfact1] = [𝒫roperfact1] _ ([𝓹roperfact1] _∼_ _⊛_) 𝔟
  𝓟roperfact1 = 𝒫roperfact1 _ ([𝓹roperfact1] _∼_ _⊛_)
