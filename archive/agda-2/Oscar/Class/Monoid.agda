
module Oscar.Class.Monoid where

open import Oscar.Data.Equality
open import Oscar.Level

record Monoid {a} {A : Set a} {b} (_↠_ : A → A → Set b) : Set (a ⊔ b) where
  field
    ε : ∀ {m} → m ↠ m
    _◇_ : ∀ {l m n} → m ↠ n → l ↠ m → l ↠ n
    ◇-left-identity : ∀ {m n} → (f : m ↠ n) → ε ◇ f ≡ f
    ◇-right-identity : ∀ {m n} → (f : m ↠ n) → f ◇ ε ≡ f
    ◇-associativity : ∀ {k l m n} (f : k ↠ l) (g : l ↠ m) (h : m ↠ n) → h ◇ (g ◇ f) ≡ (h ◇ g) ◇ f

open Monoid ⦃ … ⦄ public
