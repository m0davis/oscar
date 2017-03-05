
module Oscar.Data.Term.set {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Fin.Core
open import Oscar.Data.Nat.Core
open import Oscar.Data.Vec.Core

data Term (n : ℕ) : Set 𝔣 where
  i : (x : Fin n) → Term n
  leaf : Term n
  _fork_ : (s t : Term n) → Term n
  function : FunctionName → ∀ {f} → Vec (Term n) f → Term n
