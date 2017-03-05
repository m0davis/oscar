
module Oscar.Data.Fin.AlphaConversion where

open import Oscar.Data.Nat.Core
open import Oscar.Data.Fin.Core

_↬_ : ℕ → ℕ → Set
m ↬ n = Fin m → Fin n
