
module Oscar.Class.AlphaConversion where

open import Oscar.Data.Nat
open import Oscar.Data.Fin
open import Oscar.Data.Equality
open import Oscar.Function
open import Oscar.Relation
open import Oscar.Level

record AlphaConversion {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
  infixr 19 _◂_
  field
    _◂_ : ∀ {m n} → m ⟨ B ⟩→ n → m ⟨ C ⟩→ n
    ◂-identity : ∀ {m} (x : C m) → id ◂ x ≡ x
    ◂-associativity : ∀ {l m n} (f : l ⟨ B ⟩→ m) (g : m ⟨ B ⟩→ n) (x : C l) → (g ∘ f) ◂ x ≡ g ◂ f ◂ x
    ◂-extensionality : ∀ {m n} {f g : m ⟨ B ⟩→ n} → f ≡̇ g → f ◂_ ≡̇ g ◂_

open AlphaConversion ⦃ … ⦄ public

instance AlphaConversion⋆ : ∀ {a} {A : Set a} {bc} {BC : A → Set bc} → AlphaConversion BC BC
AlphaConversion._◂_ AlphaConversion⋆ = id
AlphaConversion.◂-identity AlphaConversion⋆ _ = refl
AlphaConversion.◂-associativity AlphaConversion⋆ _ _ _ = refl
AlphaConversion.◂-extensionality AlphaConversion⋆ f≡̇g x = f≡̇g x
