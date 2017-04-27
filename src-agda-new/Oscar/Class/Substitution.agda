
module Oscar.Class.Substitution where

open import Oscar.Data.Equality
open import Oscar.Function
open import Oscar.Relation
open import Oscar.Level

record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    ε : ∀ {m} → B m → C m
    _◇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
    ◇-left-identity : ∀ {m n} → (f : B m → C n) → ε ◇ f ≡̇ f
    ◇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇ ε ≡̇ f
    ◇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇ (g ◇ f) ≡̇ (h ◇ g) ◇ f

open Substitution ⦃ … ⦄ public

{-# DISPLAY Substitution._◇_ _ = _◇_ #-}

instance Substitution-id : ∀ {a} {A : Set a} {bc} {BC : A → Set bc} → Substitution BC BC
Substitution.ε Substitution-id = id
Substitution._◇_ Substitution-id g f = g ∘ f
Substitution.◇-left-identity Substitution-id _ _ = refl
Substitution.◇-right-identity Substitution-id _ _ = refl
Substitution.◇-associativity Substitution-id _ _ _ _ = refl
