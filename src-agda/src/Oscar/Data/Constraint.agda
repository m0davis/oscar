
open import Oscar.Prelude

module Oscar.Data.Constraint where

data Constraint {𝔞} {𝔄 : Ø 𝔞} (𝒶 : 𝔄) : Ø₀ where
  instance ∅ : Constraint 𝒶
