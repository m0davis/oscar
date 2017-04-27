
module Oscar.Data.Term {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Equality
open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Vec
open import Oscar.Function
open import Oscar.Relation

mutual

  Terms : Nat → Nat → Set 𝔣
  Terms N m = Vec (Term m) N

  data Term (m : Nat) : Set 𝔣 where
    i : (x : Fin m) → Term m
    leaf : Term m
    _fork_ : (s t : Term m) → Term m
    function : FunctionName → ∀ {N} → Terms N m → Term m
