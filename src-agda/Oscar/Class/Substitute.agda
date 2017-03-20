
module Oscar.Class.Substitute where

open import Oscar.Class.Substitution
open import Oscar.Data.Equality
open import Oscar.Function
open import Oscar.Relation
open import Oscar.Level

record Substitute {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) {d} (D : A → Set d) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    ⦃ substitution ⦄ : Substitution B C
    _◃_ : ∀ {m n} → (B m → C n) → m ⟨ D ⟩→ n
    ◃-identity : ∀ {m} → (x : D m) → ε ◃ x ≡ x
    ◃-associativity : ∀ {l m n} (f : B l → C m) (g : B m → C n) (t : D l) → (g ◇ f) ◃ t ≡ g ◃ (f ◃ t)
    ◃-extensionality : ∀ {m n} {f g : B m → C n} → f ≡̇ g → f ◃_ ≡̇ g ◃_

open Substitute ⦃ … ⦄ public

{-# DISPLAY Substitute._◃_ _ = _◃_ #-}

instance Substitute-id : ∀ {a} {A : Set a} {bcd} {BCD : A → Set bcd} → Substitute BCD BCD BCD
Substitute.substitution Substitute-id = Substitution-id
Substitute._◃_ Substitute-id = id
Substitute.◃-identity Substitute-id _ = refl
Substitute.◃-associativity Substitute-id _ _ _ = refl
Substitute.◃-extensionality Substitute-id f≡̇g = f≡̇g

-- record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) {d} (D : A → Set d) : Set (a ⊔ b ⊔ c ⊔ d) where
--   field
--     _◃_ : ∀ {m n} → (B m → C n) → m ⟨ D ⟩→ n
--     ε : ∀ {m} → B m → C m
--     ◃-identity : ∀ {m} → (x : D m) → ε ◃ x ≡ x
--     _◇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
--     ◃-associativity : ∀ {l m n} → {f : B m → C n} {g : B l → C m} (t : D l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
--     ◃-extensionality : ∀ {m n} {f g : B m → C n} → f ≡̇ g → f ◃_ ≡̇ g ◃_

-- {-
--   Unifies : ∀ {m} (s t : A m) → Property m
--   Unifies s t f = f ◃ s ≡ f ◃ t
-- -}

-- open Substitution ⦃ … ⦄ public

-- -- record Substitution {a} {A : Set a} {b} (S : A → A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- --   field
-- --     _◃_ : ∀ {m n} → S m n → m ⟨ C ⟩→ n
-- --     ε : ∀ {m} → S m m
-- --     ◃-identity : ∀ {m} → (x : C m) → ε ◃ x ≡ x
-- --     _◇_ : ∀ {l m n} → S m n → S l m → S l n

-- --   field
-- --     ◃-associativity : ∀ {l m n} → {f : S m n} {g : S l m} (t : C l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
-- --     ◃-extensionality : ∀ {m n} {f g : S m n} → f ≡ g → f ◃_ ≡̇ g ◃_

-- -- open Substitution ⦃ … ⦄ public

-- -- -- record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- -- --   field
-- -- --     _◃_ : ∀ {m n} → (B m → C n) → m ⟨ C ⟩→ n
-- -- --     ε : ∀ {m} → B m → C m
-- -- --     ◃-identity : ∀ {m} → (x : C m) → ε ◃ x ≡ x

-- -- --   _◇_ : ∀ {l m n} → (f : B m → C n) (g : B l → C m) → B l → C n
-- -- --   _◇_ f g = (f ◃_) ∘ g

-- -- --   field
-- -- --     ◃-associativity : ∀ {l m n} → {f : B m → C n} {g : B l → C m} (t : C l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
-- -- --     ◃-extensionality : ∀ {m n} {f g : B m → C n} → f ≡̇ g → f ◃_ ≡̇ g ◃_

-- -- -- {-
-- -- --   Unifies : ∀ {m} (s t : A m) → Property m
-- -- --   Unifies s t f = f ◃ s ≡ f ◃ t
-- -- -- -}

-- -- -- open Substitution ⦃ … ⦄ public

-- -- -- instance Substitution⋆ : ∀ {a} {A : Set a} {bc} {BC : A → Set bc} → Substitution BC BC
-- -- -- Substitution._◃_ Substitution⋆ = id
-- -- -- Substitution.ε Substitution⋆ = id
-- -- -- Substitution.◃-identity Substitution⋆ _ = refl
-- -- -- Substitution.◃-associativity Substitution⋆ _ = refl
-- -- -- Substitution.◃-extensionality Substitution⋆ f≡̇g x = f≡̇g x
