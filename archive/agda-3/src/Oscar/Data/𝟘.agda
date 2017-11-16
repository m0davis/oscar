
open import Oscar.Prelude

module Oscar.Data.𝟘 where

data 𝟘 : Ø₀ where

¬_ : ∀ {a} (A : Ø a) → Ø a
¬_ x = x → 𝟘
