
open import Oscar.Prelude

module Oscar.Class.[IsExtensionB] where

record [IsExtensionB]
  {a} {A : Ø a}
  {b} (B : A → Ø b)
  : Ø₀ where
  constructor ∁
  no-eta-equality
