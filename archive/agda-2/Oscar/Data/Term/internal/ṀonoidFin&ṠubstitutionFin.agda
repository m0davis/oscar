
module Oscar.Data.Term.internal.ṀonoidFin&ṠubstitutionFin {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Equality
open import Oscar.Data.Equality.properties
open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Vec
open import Oscar.Function

ε̇ : ∀ {m} → m ⊸ m
ε̇ = i

infix 19 _◃_ _◃s_
mutual

  _◃_ : ∀ {m n} → (f : m ⊸ n) → Term m → Term n
  σ̇ ◃ i 𝑥 = σ̇ 𝑥
  _ ◃ leaf = leaf
  σ̇ ◃ (τl fork τr) = (σ̇ ◃ τl) fork (σ̇ ◃ τr)
  σ̇ ◃ (function fn τs) = function fn (σ̇ ◃s τs) where

  _◃s_ : ∀ {m n} → m ⊸ n → ∀ {N} → Vec (Term m) N → Vec (Term n) N
  f ◃s [] = []
  f ◃s (t ∷ ts) = f ◃ t ∷ f ◃s ts

_◇̇_ : ∀ {l m n} → m ⊸ n → l ⊸ m → l ⊸ n
_◇̇_ f g = (f ◃_) ∘ g

mutual

  ◃-identity : ∀ {m} (t : Term m) → ε̇ ◃ t ≡ t
  ◃-identity (i x) = refl
  ◃-identity leaf = refl
  ◃-identity (s fork t) = cong₂ _fork_ (◃-identity s) (◃-identity t)
  ◃-identity (function fn ts) = cong (function fn) (◃s-identity ts)

  ◃s-identity : ∀ {N m} (t : Vec (Term m) N) → ε̇ ◃s t ≡ t
  ◃s-identity [] = refl
  ◃s-identity (t ∷ ts) = cong₂ _∷_ (◃-identity t) (◃s-identity ts)

◇̇-left-identity : ∀ {m n} (f : m ⊸ n) → ε̇ ◇̇ f ≡̇ f
◇̇-left-identity f = ◃-identity ∘ f

◇̇-right-identity : ∀ {m n} (f : m ⊸ n) → f ◇̇ ε̇ ≡̇ f
◇̇-right-identity _ _ = refl

mutual

  ◃-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◃_ ≡̇ g ◃_
  ◃-extensionality p (i x) = p x
  ◃-extensionality p leaf = refl
  ◃-extensionality p (s fork t) = cong₂ _fork_ (◃-extensionality p s) (◃-extensionality p t)
  ◃-extensionality p (function fn ts) = cong (function fn) (◃s-extensionality p ts)

  ◃s-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → ∀ {N} → _◃s_ f {N} ≡̇ _◃s_ g {N}
  ◃s-extensionality p [] = refl
  ◃s-extensionality p (t ∷ ts) = cong₂ _∷_ (◃-extensionality p t) (◃s-extensionality p ts)

mutual

  ◃-associativity : ∀ {l m n} (f : l ⊸ m) (g : m ⊸ n) (t : Term l) → (g ◇̇ f) ◃ t ≡ g ◃ (f ◃ t)
  ◃-associativity _ _ (i _) = refl
  ◃-associativity _ _ leaf = refl
  ◃-associativity _ _ (τ₁ fork τ₂) = cong₂ _fork_ (◃-associativity _ _ τ₁) (◃-associativity _ _ τ₂)
  ◃-associativity f g (function fn ts) = cong (function fn) (◃s-associativity f g ts)

  ◃s-associativity : ∀ {l m n} (f : l ⊸ m) (g : m ⊸ n) → ∀ {N} (t : Vec (Term l) N) → (g ◇̇ f) ◃s t ≡ g ◃s (f ◃s t)
  ◃s-associativity _ _ [] = refl
  ◃s-associativity _ _ (τ ∷ τs) = cong₂ _∷_ (◃-associativity _ _ τ) (◃s-associativity _ _ τs)

◇̇-associativity : ∀ {k l m n} (f : k ⊸ l) (g : l ⊸ m) (h : m ⊸ n) → h ◇̇ (g ◇̇ f) ≡̇ (h ◇̇ g) ◇̇ f
◇̇-associativity f g h x rewrite ◃-associativity g h (f x) = refl
