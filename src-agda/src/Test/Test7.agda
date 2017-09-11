
open import Everything

module Test.Test7 where

  𝓅rop-id-1 𝓅rop-id-2 : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : Transitivity.class _∼_ ⦄
    ⦃ _ : Reflexivity.class _∼_ ⦄
    ⦃ _ : Transleftidentity!.class _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    {m n}
    {ℓ} {f : m ∼ n} (P : ExtensionṖroperty ℓ (Arrow 𝔄 𝔅 m) _∼̇_) (let P₀ = π₀ (π₀ P))
    → P₀ f
    → P₀ (ε ∙ f)

  𝓅rop-id-1 P Pf = smap {y = P} Pf
  𝓅rop-id-2 P Pf = hmap _ P Pf
