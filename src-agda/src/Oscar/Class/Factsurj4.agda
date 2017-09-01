
open import Oscar.Prelude
open import Oscar.Class.Leftstar
open import Oscar.Class.Smap
open import Oscar.Class.Surjection

module Oscar.Class.Factsurj4 where

open import Oscar.Data.Constraint

module _
  {𝔞} {𝔄 : Ø 𝔞}
  ⦃ _ : Surjection.class 𝔄 𝔄 ⦄
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
  {𝔡} (𝔇 : ∀ {a} → 𝔅 (surjection a) → Ø 𝔡)
  ⦃ _ : Surjectextensivity.class ℭ 𝔅 ⦄
  where
  𝓕actsurj4 = ∀ {a₁ a₂} → LEFTSTAR.∁⟦ 𝔇 {a₁} / 𝔇 {a₂} / surjectextensivity {x = a₁} {a₂} ⟧
