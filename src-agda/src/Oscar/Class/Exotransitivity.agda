
open import Oscar.Prelude

module Oscar.Class.Exotransitivity where

record Exotransitivity
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  {𝔟} (𝔅 : 𝔛 → 𝔛 → Ø 𝔟)
  : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟
  where
  field
    exotransitivity : ∀ {x y} → 𝔅 x y → 𝔄 x → 𝔄 y
