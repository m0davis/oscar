
module Oscar.Class.Ṁonoid where

open import Oscar.Data.Equality
open import Oscar.Level

record Ṁonoid {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    ε̇ : ∀ {m} → B m → C m
    _◇̇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
    ◇̇-left-identity : ∀ {m n} → (f : B m → C n) → ε̇ ◇̇ f ≡̇ f
    ◇̇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇̇ ε̇ ≡̇ f
    ◇̇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇̇ (g ◇̇ f) ≡̇ (h ◇̇ g) ◇̇ f

open Ṁonoid ⦃ … ⦄ public
