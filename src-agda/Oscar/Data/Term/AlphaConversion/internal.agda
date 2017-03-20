
module Oscar.Data.Term.AlphaConversion.internal {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term FunctionName

open import Oscar.Data.Equality
open import Oscar.Data.Fin
open import Oscar.Data.Vec
open import Oscar.Function
open import Oscar.Relation

infixr 19 _◂_ _◂s_

mutual

  _◂_ : ∀ {m n} → m ⟨ Fin ⟩→ n → m ⟨ Term ⟩→ n
  _◂_ f (i 𝑥) = i (f 𝑥)
  _◂_ f leaf = leaf
  _◂_ f (τ₁ fork τ₂) = (f ◂ τ₁) fork (f ◂ τ₂)
  _◂_ f (function 𝑓 τs) = function 𝑓 (f ◂s τs)

  _◂s_ : ∀ {m n} → m ⟨ Fin ⟩→ n → ∀ {N} → m ⟨ Terms N ⟩→ n
  _◂s_ f [] = []
  _◂s_ f (τ ∷ τs) = f ◂ τ ∷ f ◂s τs

mutual

  ◂-identity : ∀ {m} (τ : Term m) → id ◂ τ ≡ τ
  ◂-identity (i _) = refl
  ◂-identity leaf = refl
  ◂-identity (τ₁ fork τ₂) rewrite ◂-identity τ₁ | ◂-identity τ₂ = refl
  ◂-identity (function 𝑓 τs) rewrite ◂s-identity τs = refl

  ◂s-identity : ∀ {N m} (τs : Terms N m) → id ◂s τs ≡ τs
  ◂s-identity [] = refl
  ◂s-identity (τ ∷ τs) rewrite ◂-identity τ | ◂s-identity τs = refl

mutual

  ◂-associativity : ∀ {l m n} (f : l ⟨ Fin ⟩→ m) (g : m ⟨ Fin ⟩→ n) → (τ : Term l) → (g ∘ f) ◂ τ ≡ g ◂ f ◂ τ
  ◂-associativity _ _ (i _) = refl
  ◂-associativity _ _ leaf = refl
  ◂-associativity f g (τ₁ fork τ₂) rewrite ◂-associativity f g τ₁ | ◂-associativity f g τ₂ = refl
  ◂-associativity f g (function 𝑓 τs) rewrite ◂s-associativity f g τs = refl

  ◂s-associativity : ∀ {l m n} (f : l ⟨ Fin ⟩→ m) (g : m ⟨ Fin ⟩→ n) → ∀ {N} (x : Terms N l) → (g ∘ f) ◂s x ≡ g ◂s f ◂s x
  ◂s-associativity _ _ [] = refl
  ◂s-associativity f g (τ ∷ τs) rewrite ◂-associativity f g τ | ◂s-associativity f g τs = refl

mutual

  ◂-extensionality : ∀ {m n} {f g : m ⟨ Fin ⟩→ n} → f ≡̇ g → f ◂_ ≡̇ g ◂_
  ◂-extensionality f≡̇g (i 𝑥) rewrite f≡̇g 𝑥 = refl
  ◂-extensionality f≡̇g leaf = refl
  ◂-extensionality f≡̇g (τ₁ fork τ₂) rewrite ◂-extensionality f≡̇g τ₁ | ◂-extensionality f≡̇g τ₂ = refl
  ◂-extensionality f≡̇g (function 𝑓 τs) rewrite ◂s-extensionality f≡̇g τs = refl

  ◂s-extensionality : ∀ {m n} {f g : m ⟨ Fin ⟩→ n} → f ≡̇ g → ∀ {N} → _◂s_ f {N} ≡̇ _◂s_ g {N}
  ◂s-extensionality _ [] = refl
  ◂s-extensionality f≡̇g (τ ∷ τs) rewrite ◂-extensionality f≡̇g τ | ◂s-extensionality f≡̇g τs = refl
