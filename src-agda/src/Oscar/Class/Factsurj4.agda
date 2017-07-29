
open import Oscar.Prelude
open import Oscar.Class.Surjectextensivity

module Oscar.Class.Factsurj4 where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
  {𝔡} (𝔇 : ∀ {a} → 𝔅 a → Ø 𝔡)
  where
  record [𝓕actsurj4] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓢urjectextensivity ℭ 𝔅 ⦄
    ⦃ _ : [𝓕actsurj4] ⦄
    where
    𝓯actsurj4 = ∀ {a₁ a₂} {b : 𝔅 a₁} (c : ℭ a₁ a₂) → 𝔇 b → 𝔇 (c ◃ b)
    record 𝓕actsurj4 : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where field factsurj4 : 𝓯actsurj4

open 𝓕actsurj4 ⦃ … ⦄ public
