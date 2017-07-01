
module Oscar.Class.Functor where

open import Oscar.Class.Monoid
open import Oscar.Data.Equality
open import Oscar.Data.Product
open import Oscar.Level
open import Oscar.Relation
open import Oscar.Function

record Functor {a} {A : Set a} {b} (_↠_ : A → A → Set b) ⦃ _ : Monoid _↠_ ⦄ {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
  field
    _◃_ : ∀ {m n} → m ↠ n → m ⟨ C ⟩→ n
    ◃-identity : ∀ {m} → (x : C m) → ε ◃ x ≡ x
    ◃-associativity : ∀ {l m n} (f : l ↠ m) (g : m ↠ n) → (g ◇ f) ◃_ ≡̇ g ◃_ ∘ f ◃_
    ◃-extensionality : ∀ {m n} {f g : m ↠ n} → f ≡ g → f ◃_ ≡ g ◃_

open Functor ⦃ … ⦄ public

open import Data.List
open import Oscar.Function

instance MonoidFunction : ∀ {a} → Monoid {A = Set a} (λ m n → m → n)
Monoid.ε MonoidFunction = λ x → x
Monoid._◇_ MonoidFunction g f = g ∘ f
Monoid.◇-left-identity MonoidFunction _ = refl
Monoid.◇-right-identity MonoidFunction _ = refl
Monoid.◇-associativity MonoidFunction _ _ _ = refl

instance FunctorList : ∀ {a} → Functor _ ⦃ MonoidFunction {a} ⦄ List
Functor._◃_ FunctorList {m} {n} f [] = []
Functor._◃_ FunctorList {m} {n} f (x ∷ xs) = f x ∷ f ◃ xs
Functor.◃-identity FunctorList = {!!}
Functor.◃-associativity FunctorList = {!!}
Functor.◃-extensionality FunctorList = {!!}
