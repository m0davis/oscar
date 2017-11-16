
open import Oscar.Prelude
open import Oscar.Data.𝟘

module Oscar.Data.Decidable where

data Decidable {a} (A : Ø a) : Ø a where
  ↑_ : A → Decidable A
  ↓_ : ¬ A → Decidable A
