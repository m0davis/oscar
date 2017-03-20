
module Oscar.Class.TermSubstitution.Internal {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Nat.Core
open import Oscar.Data.Fin.Core
open import Oscar.Data.Vec.Core
open import Oscar.Data.Equality.Core
open import Oscar.Data.Product.Core
open import Oscar.Function
open import Oscar.Level

_⊸_ : (m n : ℕ) → Set 𝔣
m ⊸ n = Fin m → Term n

⊸-Property : {ℓ : Level} → ℕ → Set (lsuc ℓ ⊔ 𝔣)
⊸-Property {ℓ} m = ∀ {n} → m ⊸ n → Set ℓ

_≐_ : {m n : ℕ} → m ⊸ n → m ⊸ n → Set 𝔣
f ≐ g = ∀ x → f x ≡ g x

⊸-Extensional : {ℓ : Level} {m : ℕ} → ⊸-Property {ℓ} m → Set (ℓ ⊔ 𝔣)
⊸-Extensional P = ∀ {m f g} → f ≐ g → P {m} f → P g

⊸-ExtentionalProperty : {ℓ : Level} → ℕ → Set (lsuc ℓ ⊔ 𝔣)
⊸-ExtentionalProperty {ℓ} m = Σ (⊸-Property {ℓ} m) ⊸-Extensional

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
