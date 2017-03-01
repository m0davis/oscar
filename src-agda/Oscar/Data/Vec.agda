
module Oscar.Data.Vec where

open import Data.Vec public

--open import Data.Product
open import Data.Nat

map₂ : ∀ {a b} {A : Set a} {B : Set b} {m n}
           → ∀ {c} {C : Set c} (f : A → B → C)
           → Vec A m → Vec B n → Vec C (m * n)
map₂ f xs ys = map f xs ⊛* ys

open import Data.Fin

delete : ∀ {a n} {A : Set a} → Fin (suc n) → Vec A (suc n) → Vec A n
delete zero (x ∷ xs) = xs
delete {n = zero} (suc ()) _
delete {n = suc n} (suc i) (x ∷ xs) = x ∷ delete i xs

open import Function

-- tabulate⋆ : ∀ {n a} {A : Set a} → (F : Fin n → A) → ∃ λ (v : Vec A n) → ∀ (i : Fin n) → F i ∈ v
-- tabulate⋆ {zero} F = [] , (λ ())
-- tabulate⋆ {suc n} F = let v , t = tabulate⋆ (F ∘ suc) in F zero ∷ v , (λ { zero → here ; (suc i) → there (t i)})
