
module Oscar.Class.AlphaConversion where

open import Oscar.Data.Nat.Core
open import Oscar.Data.Fin.Core
open import Oscar.Data.Fin.AlphaConversion
open import Oscar.Data.Equality.Core
open import Oscar.Function
open import Oscar.Class.ExtensionalEquality

record AlphaConversion {a} (A : ℕ → Set a) : Set a where
  field
    _◂_ : ∀ {m n} → m ↬ n → A m → A n
    ◂-identity : ∀ {m} (x : A m) → id ◂ x ≡ x
    ◂-associativity : ∀ {l m n} {f : m ↬ n} {g : l ↬ m} → (x : A l) → (f ∘ g) ◂ x ≡ f ◂ (g ◂ x)

  instance ExtensionalEqualityAlphaConversion : ∀ {m n} → ExtensionalEquality (A m) (λ _ → A n)
  ExtensionalEqualityAlphaConversion = record { _≐_ = λ f g → ∀ x → f x ≡ g x }

  field
    ◂-extensionality : ∀ {m n} {f g : m ↬ n} → f ≐ g → (f ◂_) ≐ (g ◂_)
