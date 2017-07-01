
module Oscar.Class where

open import Oscar.Data.Equality
open import Oscar.Function
open import Oscar.Relation
open import Oscar.Level
open import Oscar.Function
open import Oscar.Relation

-- instance EquivalenceProp : ∀ {a} {A : Set a} → Equivalence (_≡_ {a} {A})
-- EquivalenceProp = {!!}

-- instance EquivalenceProp1 : ∀ {a} {A : Set a} {b} {B : A → Set b} → Equivalence (_≡̇_ {a} {A} {b} {B})
-- Equivalence.reflexivity EquivalenceProp1 x x₁ = refl

-- import Oscar.Data.Term.internal.SubstituteAndSubstitution FunctionName as ⋆

-- instance SemigroupFinTerm : Semigroup _⊸_ _≡̇_
-- Semigroup.equivalence SemigroupFinTerm = it
-- Semigroup._◇_ SemigroupFinTerm = ⋆._◇_ -- (Semifunctor._◃ SemifunctorFinTerm g) ∘ f --
-- Semigroup.◇-associativity SemigroupFinTerm = {!!}

-- instance Semigroup⋆ : ∀ {a} {A : Set a} {x} {X : A → Set x} → Semigroup (_⟨ X ⟩→_) _≡̇_
-- Semigroup.equivalence Semigroup⋆ = it
-- Semigroup._◇_ Semigroup⋆ g f = g ∘ f
-- Semigroup.◇-associativity Semigroup⋆ = {!!}

-- instance SemifunctorFinTerm : Semifunctor _⊸_ _≡̇_ (_⟨ Term ⟩→_) _≡̇_ id
-- Semifunctor.domain SemifunctorFinTerm = it
-- Semifunctor.codomain SemifunctorFinTerm = it
-- SemifunctorFinTerm Semifunctor.◃ = ⋆._◃_
-- Semifunctor.◃-extensionality SemifunctorFinTerm = ⋆.◃-extensionality
-- Semifunctor.◃-associativity SemifunctorFinTerm = ⋆.◃-associativity

-- -- sufficient for all my substitutions (Term, Formula, etc.)
-- _◂_ : ∀ {m n a} {A : Nat → Set a} ⦃ _ : Semifunctor _⊸_ _≡̇_ (_⟨ A ⟩→_) _≡̇_ id ⦄ → m ⊸ n → m ⟨ A ⟩→ n
-- _◂_ ⦃ semifunctor ⦄ f x = Semifunctor._◃ semifunctor f x

-- -- even more general, handling all pointwise (semi)functors
-- _◂'_ : ∀ {a} {A : Set a} {m n : A} {b} {B : A → Set b} {c} {C : A → Set c} {d} {D : A → Set d}
--          ⦃ _ : Semifunctor (λ m n → B m → C n) _≡̇_ _⟨ D ⟩→_ _≡̇_ id ⦄ → (B m → C n) → m ⟨ D ⟩→ n
-- _◂'_ ⦃ semifunctor ⦄ f x = Semifunctor._◃ semifunctor f x

-- record UsableSemifunctor {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) {d} (D : A → Set d) : Set (a ⊔ b ⊔ c ⊔ d) where
--   field
--     ⦃ semifunctor ⦄ : Semifunctor (λ m n → B m → C n) _≡̇_ _⟨ D ⟩→_ _≡̇_ id

--   _◄_ : ∀ {m n} → (B m → C n) → m ⟨ D ⟩→ n
--   _◄_ f x = Semifunctor._◃ semifunctor f x

-- open UsableSemifunctor ⦃ … ⦄

-- instance UsableSemifunctor⋆ : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : A → Set c} {d} {D : A → Set d}
--                               -- { _≋₁_ : ∀ {m n} → (B m → C n) → (B m → C n) → Set (b ⊔ c) }
--                               -- ⦃ _ : ∀ {m n} → Equivalence (_≋₁_ {m} {n}) ⦄
--                               -- ⦃ _ : Semifunctor (λ m n → B m → C n) _≋₁_ _⟨ D ⟩→_ _≡̇_ id ⦄ → UsableSemifunctor B C D
--                               ⦃ _ : Semifunctor (λ m n → B m → C n) _≡̇_ _⟨ D ⟩→_ _≡̇_ id ⦄
--                               → UsableSemifunctor B C D
-- UsableSemifunctor.semifunctor (UsableSemifunctor⋆ ⦃ semi ⦄) = semi

-- {-
-- instance UsableSemifunctorFinTermTerm : UsableSemifunctor Fin Term Term
-- UsableSemifunctor.semifunctor UsableSemifunctorFinTermTerm = it
-- -}

-- -- obviously won't work unless we supply _≋₁_
-- _◂''_ : ∀ {a} {A : Set a} {m n : A} {b} {B : A → Set b} {c} {C : A → Set c} {d} {D : A → Set d}
--         ( _≋₁_ : ∀ {m n} → (B m → C n) → (B m → C n) → Set (b ⊔ c) )
--         ⦃ _ : ∀ {m n} → Equivalence (_≋₁_ {m} {n}) ⦄
--         ⦃ _ : Semifunctor (λ m n → B m → C n) _≋₁_ _⟨ D ⟩→_ _≡̇_ id ⦄ → (B m → C n) → m ⟨ D ⟩→ n
-- _◂''_ _ ⦃ _ ⦄ ⦃ semifunctor ⦄ f x = Semifunctor._◃ semifunctor f x

-- foo : ∀ {m n} → m ⊸ n → Term m → Term n
-- foo {m} {n} f x = f ◄ x

-- --foo f x = f ◂ x
-- --foo f x = _◂''_ _≡̇_ f x


-- -- record Ṁonoid {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- --   field
-- --     ε̇ : ∀ {m} → B m → C m
-- --     _◇̇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
-- --     ◇̇-left-identity : ∀ {m n} → (f : B m → C n) → ε̇ ◇̇ f ≡̇ f
-- --     ◇̇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇̇ ε̇ ≡̇ f
-- --     ◇̇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇̇ (g ◇̇ f) ≡̇ (h ◇̇ g) ◇̇ f

-- -- record Monoid {a} {A : Set a} {b} (_↠_ : A → A → Set b) : Set (a ⊔ b) where
-- --   field
-- --     ε : ∀ {m} → m ↠ m
-- --     _◇_ : ∀ {l m n} → m ↠ n → l ↠ m → l ↠ n
-- --     ◇-left-identity : ∀ {m n} → (f : m ↠ n) → ε ◇ f ≡ f
-- --     ◇-right-identity : ∀ {m n} → (f : m ↠ n) → f ◇ ε ≡ f
-- --     ◇-associativity : ∀ {k l m n} (f : k ↠ l) (g : l ↠ m) (h : m ↠ n) → h ◇ (g ◇ f) ≡ (h ◇ g) ◇ f

-- -- record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- --   field
-- --     ε : ∀ {m} → B m → C m
-- --     _◇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
-- --     ◇-left-identity : ∀ {m n} → (f : B m → C n) → ε ◇ f ≡̇ f
-- --     ◇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇ ε ≡̇ f
-- --     ◇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇ (g ◇ f) ≡̇ (h ◇ g) ◇ f

-- -- record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- --   field
-- --     ε : ∀ {m} → B m → C m
-- --     _◇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
-- --     ◇-left-identity : ∀ {m n} → (f : B m → C n) → ε ◇ f ≡̇ f
-- --     ◇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇ ε ≡̇ f
-- --     ◇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇ (g ◇ f) ≡̇ (h ◇ g) ◇ f

-- -- record Substitution {a} {A : Set a} {b} (B : A → Set b) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
-- --   field
-- --     ε : ∀ {m} → B m → C m
-- --     _◇_ : ∀ {l m n} → (g : B m → C n) (f : B l → C m) → B l → C n
-- --     ◇-left-identity : ∀ {m n} → (f : B m → C n) → ε ◇ f ≡̇ f
-- --     ◇-right-identity : ∀ {m n} → (f : B m → C n) → f ◇ ε ≡̇ f
-- --     ◇-associativity : ∀ {k l m n} (f : B k → C l) (g : B l → C m) (h : B m → C n) → h ◇ (g ◇ f) ≡̇ (h ◇ g) ◇ f
