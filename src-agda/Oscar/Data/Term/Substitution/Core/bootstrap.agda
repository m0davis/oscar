
module Oscar.Data.Term.Substitution.Core.bootstrap {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Nat.Core
open import Oscar.Data.Fin.Core
open import Oscar.Data.Vec.Core
open import Oscar.Function

_⊸_ : (m n : ℕ) → Set 𝔣
m ⊸ n = Fin m → Term n

mutual

  _◃Term_ : ∀ {m n} → (f : m ⊸ n) → Term m → Term n
  f ◃Term i x = f x
  f ◃Term leaf = leaf
  f ◃Term (s fork t) = (f ◃Term s) fork (f ◃Term t)
  f ◃Term (function fn ts) = function fn (f ◃VecTerm ts) where

  _◃VecTerm_ : ∀ {N m n} → m ⊸ n → Vec (Term m) N → Vec (Term n) N
  f ◃VecTerm [] = []
  f ◃VecTerm (t ∷ ts) = f ◃Term t ∷ f ◃VecTerm ts

_◇_ : ∀ {l m n} → m ⊸ n → l ⊸ m → l ⊸ n
_◇_ f g = (f ◃Term_) ∘ g
