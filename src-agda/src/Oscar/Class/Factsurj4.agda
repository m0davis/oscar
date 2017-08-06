
open import Oscar.Prelude
open import Oscar.Class.Leftstar
open import Oscar.Class.Surjectextensivity
import Oscar.Class.Surjection.⋆

module Oscar.Class.Factsurj4 where

open import Oscar.Data.Constraint

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
  {𝔡} (𝔇 : ∀ {a} → 𝔅 a → Ø 𝔡)
  ⦃ _ : 𝓢urjectextensivity ℭ 𝔅 ⦄
  where
  𝓕actsurj4 = ∀ {a₁ a₂} → Leftstar (𝔇 {a₁}) (𝔇 {a₂}) (surjectextensivity {x = a₁} {a₂})
