
module Oscar.Class.Preservativity where

open import Oscar.Level
open import Oscar.Relation

record Preservativity
  {a} {A : Set a} {b} {B : A → Set b} {c} {C : (x : A) → B x → Set c}
    (_▻₁_ : (x : A) → (y : B x) → C x y)
  {d} {D : Set d} {e} {E : D → Set e} {f} {F : (x : D) → E x → Set f}
    (_▻₂_ : (x : D) → (y : E x) → F x y)
  {ℓ}
    (_≤_ : ∀ {x y} → F x y → F x y → Set ℓ)
    (◽ : A → D)
    (◻ : ∀ {x} → B x → E (◽ x))
    (□ : ∀ {x y} → C x y → F (◽ x) (◻ y))
  : Set (a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f ⊔ ℓ) where
  field
    preservativity : ∀ (x : A) (y : B x) → □ (x ▻₁ y) ≤ (◽ x ▻₂ ◻ y)

open Preservativity ⦃ … ⦄ public

-- -- record Preservativity
-- --   {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁}
-- --     (_◅₁_ : ∀ {m n} → m ►₁ n → ∀ {l} → m ⟨ l ►₁_ ⟩→ n)
-- --   {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} (_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂)
-- --     (_◅₂_ : ∀ {m n} → m ►₂ n → ∀ {l} → m ⟨ l ►₂_ ⟩→ n)
-- --   {ℓ}
-- --     (_≤_ : ∀ {m n} → m ►₂ n → m ►₂ n → Set ℓ)
-- --   {μ : 𝔄₁ → 𝔄₂}
-- --     (◽ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n)
-- --   : Set (𝔞₁ ⊔ 𝔰₁ ⊔ 𝔞₂ ⊔ 𝔰₂ ⊔ ℓ) where
-- --   field
-- --     preservativity : ∀ {l m} (f : l ►₁ m) {n} (g : m ►₁ n) → ◽ (g ◅₁ f) ≤ (◽ g ◅₂ ◽ f)

-- -- open Preservativity ⦃ … ⦄ public

-- -- -- record Preservativity
-- -- --   {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁}
-- -- --     (_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁) {𝔱₁}
-- -- --   {▸₁ : 𝔄₁ → Set 𝔱₁}
-- -- --     (_◃₁_ : ∀ {m n} → m ►₁ n → m ⟨ ▸₁ ⟩→ n)
-- -- --   {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂}
-- -- --     (_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂) {𝔱₂}
-- -- --   {▸₂ : 𝔄₂ → Set 𝔱₂}
-- -- --     (_◃₂_ : ∀ {m n} → m ►₂ n → m ⟨ ▸₂ ⟩→ n)
-- -- --   {ℓ}
-- -- --     (_≤_ : ∀ {n} → ▸₂ n → ▸₂ n → Set ℓ)
-- -- --   {μ : 𝔄₁ → 𝔄₂}
-- -- --     (◽ : ∀ {n} → ▸₁ n → ▸₂ (μ n))
-- -- --     (□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n)
-- -- --   : Set (𝔞₁ ⊔ 𝔰₁ ⊔ 𝔱₁ ⊔ 𝔞₂ ⊔ 𝔰₂ ⊔ 𝔱₂ ⊔ ℓ) where
-- -- --   field
-- -- --     preservativity : ∀ {m n} (f : ▸₁ m) (g : m ►₁ n) → ◽ (g ◃₁ f) ≤ (□ g ◃₂ ◽ f)

-- -- -- open Preservativity ⦃ … ⦄ public

-- -- -- open import Oscar.Class.Associativity
-- -- -- open import Oscar.Class.Symmetry
-- -- -- open import Oscar.Function

-- -- -- instance

-- -- --   Preservativity⋆ : ∀
-- -- --     {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- --       {_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n}
-- -- --     {𝔱} {▸ : 𝔄 → Set 𝔱}
-- -- --       {_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n}
-- -- --     {ℓ}
-- -- --       {_≤_ : ∀ {n} → ▸ n → ▸ n → Set ℓ}
-- -- --     ⦃ _ : Associativity _◅_ _◃_ _≤_ ⦄
-- -- --     → ∀ {n} {x : ▸ n}
-- -- --     → Preservativity _►_ (λ ⋆ → _◅_ ⋆) _►_ _◃_ (flip _≤_) (_◃ x) id
-- -- --   Preservativity.preservativity (Preservativity⋆ {_◅_ = _◅_} {_◃_ = _◃_} {_≤_ = _≤_} ⦃ ′associativity ⦄ {x = x}) f = associativity {_◅_ = _◅_} {_◃_ = _◃_} {_≤_ = _≤_} ⦃ {-′associativity-}_ ⦄ x f

-- -- -- preservation : ∀
-- -- --   {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁} {𝔱₁} {▸₁ : 𝔄₁ → Set 𝔱₁}
-- -- --     (_◃₁_ : ∀ {m n} → m ►₁ n → m ⟨ ▸₁ ⟩→ n)
-- -- --   {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} {_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂} {𝔱₂} {▸₂ : 𝔄₂ → Set 𝔱₂}
-- -- --     (_◃₂_ : ∀ {m n} → m ►₂ n → m ⟨ ▸₂ ⟩→ n)
-- -- --   {ℓ}
-- -- --     (_≤_ : ∀ {n} → ▸₂ n → ▸₂ n → Set ℓ)
-- -- --   {μ : 𝔄₁ → 𝔄₂}
-- -- --   {◽ : ∀ {n} → ▸₁ n → ▸₂ (μ n)}
-- -- --   {□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n}
-- -- --   ⦃ _ : Preservativity _►₁_ _◃₁_ _►₂_ _◃₂_ _≤_ ◽ □ ⦄
-- -- --   {m n} (f : ▸₁ m) (g : m ►₁ n) → ◽ (g ◃₁ f) ≤ (□ g ◃₂ ◽ f)
-- -- -- preservation _◃₁_ _◃₂_ _≤_ f g = preservativity {_◃₁_ = _◃₁_} {_◃₂_ = _◃₂_} {_≤_ = _≤_} f g
