
open import Oscar.Prelude

module Oscar.Class.Amgu where

record Amgu {𝔵} {X : Ø 𝔵} {𝔱} (T : X → Ø 𝔱) {𝔞} (A : X → Ø 𝔞) {𝔪} (M : Ø 𝔞 → Ø 𝔪) : Ø 𝔵 ∙̂ 𝔱 ∙̂ 𝔞 ∙̂ 𝔪 where
  field amgu : ∀ {x} → T x → T x → A x → M (A x)

open Amgu ⦃ … ⦄ public
