
open import Oscar.Prelude

module Oscar.Class.Factsurj4 where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
  where
  𝓯actsurj4-act = ∀ {a₁ a₂} → ℭ a₁ a₂ → 𝔅 a₁ → 𝔅 a₂
  module _
    {𝔡} (𝔇 : ∀ {a} → 𝔅 a → Ø 𝔡)
    where
    record [𝓕actsurj4] : Ø 𝔞 ∙̂ 𝔠 ∙̂ 𝔟 where
      constructor ∁
      field
        act : 𝓯actsurj4-act
    module _
      (act : 𝓯actsurj4-act)
      where
      𝓯actsurj4 = ∀ {a₁ a₂} {b : 𝔅 a₁} (c : ℭ a₁ a₂) → 𝔇 b → 𝔇 (act c b)
    module _
      ⦃ ⌶[𝓕actsurj4] : [𝓕actsurj4] ⦄
      where
      open [𝓕actsurj4] ⌶[𝓕actsurj4]
      record 𝓕actsurj4 : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
        field factsurj4 : 𝓯actsurj4 act

open 𝓕actsurj4 ⦃ … ⦄ public
