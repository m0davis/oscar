
module Oscar.Class.TermSubstitution {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Term.Substitution FunctionName
open import Oscar.Data.Nat.Core
open import Oscar.Data.Equality.Core
open import Oscar.Level

record Substitution {a} (A : ℕ → Set a) : Set (a ⊔ 𝔣) where
  field
    _◃_ : ∀ {m n} → m ⊸ n → A m → A n
    ◃-extentionality : ∀ {m n} {f g : m ⊸ n} → f ≐ g → (t : A m) → f ◃ t ≡ g ◃ t
    ◃-identity : ∀ {n} → (t : A n) → i ◃ t ≡ t

  field
    ◃-associativity : ∀ {l m n} → {f : m ⊸ n} {g : _} (t : A l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)

  ⊸-Unifies : ∀ {m} (s t : A m) → ⊸-Property m
  ⊸-Unifies s t f = f ◃ s ≡ f ◃ t

open Substitution ⦃ … ⦄ public

{-# DISPLAY Substitution._◃_ _ = _◃_ #-}
