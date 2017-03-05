
module Oscar.Data.Term.Substitution {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Substitution.Core FunctionName public

open import Oscar.Class.ThickAndThin
open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Fin
open import Oscar.Data.Nat.Core
open import Oscar.Data.Vec.Core
open import Oscar.Data.Product.Core
open import Oscar.Data.Equality
open import Oscar.Data.Maybe
open import Oscar.Function
open import Oscar.Level

▹ : ∀ {m n} → (Fin m → Fin n) → m ⊸ n
▹ r = i ∘ r

≐-sym : ∀ {m n} {f : m ⊸ n} {g} → f ≐ g → g ≐ f
≐-sym f≐g = sym ∘ f≐g

_for_ : ∀ {n} (t' : Term n) (x : Fin (suc n)) -> Fin (suc n) -> Term n
(t' for x) y = maybe i t' (check x y)
