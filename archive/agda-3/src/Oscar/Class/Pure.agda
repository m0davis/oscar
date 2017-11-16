
open import Oscar.Prelude

module Oscar.Class.Pure where

module _
  {𝔬 𝔣}
  (𝔉 : Ø 𝔬 → Ø 𝔣)
  where
  𝓹ure = ∀ {𝔒 : Ø 𝔬} → 𝔒 → 𝔉 𝔒
  record 𝓟ure : Ø 𝔣 ∙̂ ↑̂ 𝔬 where
    field pure : 𝓹ure
open 𝓟ure ⦃ … ⦄ public
