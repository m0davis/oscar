
module Oscar.Class.Ḟunctor where

open import Oscar.Class.Ṁonoid
open import Oscar.Data.Equality
open import Oscar.Level
open import Oscar.Relation

record Ḟunctor {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) ⦃ _ : Ṁonoid B C ⦄ {d} (D : A → Set d) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    _◃̇_ : ∀ {m n} → (B m → C n) → m ⟨ D ⟩→ n
    ◃̇-identity : ∀ {m} → (x : D m) → ε̇ ◃̇ x ≡ x
    ◃̇-associativity : ∀ {l m n} (f : B l → C m) (g : B m → C n) (t : D l) → (g ◇̇ f) ◃̇ t ≡ g ◃̇ (f ◃̇ t)
    ◃̇-extensionality : ∀ {m n} {f g : B m → C n} → f ≡̇ g → f ◃̇_ ≡̇ g ◃̇_

open Ḟunctor ⦃ … ⦄ public
