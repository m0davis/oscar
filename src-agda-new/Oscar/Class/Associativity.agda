
module Oscar.Class.Associativity where

open import Oscar.Class.Preservativity
open import Oscar.Function
open import Oscar.Level
open import Oscar.Relation

record Associativity
  {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
    (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
  {ℓ}
    (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
  : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
  field
    associativity : ∀ {k l} (f : k ► l) {m} (g : l ► m) {n} (h : m ► n) → (h ◅ (g ◅ f)) ≤ ((h ◅ g) ◅ f)

  instance `preservativity : ∀ {l} {m} {n} {w : m ► n} → Preservativity (λ ⋆ → _◅_ ⋆) (λ ⋆ → _◅_ ⋆) _≤_ (m ⟨ l ►_ ⟩→ n ∋ w ◅_) id (m ⟨ l ►_ ⟩→ n ∋ w ◅_)
  Preservativity.preservativity `preservativity g f = associativity f g _
--    ⦃ `preservativity ⦄ : ∀ {l} {m} {n} {w : m ► n} → Preservativity (λ ⋆ → _◅_ ⋆) (λ ⋆ → _◅_ ⋆) _≤_ (m ⟨ l ►_ ⟩→ n ∋ w ◅_) id (m ⟨ l ►_ ⟩→ n ∋ w ◅_)

open Associativity ⦃ … ⦄ public

module _ where

  private

    postulate
      A : Set
      _⇒_ : A → A → Set
      _∙_ : ∀ {m n} → m ⇒ n → ∀ {l} → m ⟨ l ⇒_ ⟩→ n
      _≋_ : ∀ {m n} → m ⇒ n → m ⇒ n → Set
      instance _ : Associativity _∙_ _≋_

    test-associativity₁ : ∀ {k l} (f : k ⇒ l) {m} (g : l ⇒ m) {n} (h : m ⇒ n) → (h ∙ (g ∙ f)) ≋ ((h ∙ g) ∙ f)
    test-associativity₁ = associativity {_◅_ = _∙_}

    test-associativity₂ : ∀ {k l} (f : k ⇒ l) {m} (g : l ⇒ m) {n} (h : m ⇒ n) → (h ∙ (g ∙ f)) ≋ ((h ∙ g) ∙ f)
    test-associativity₂ = associativity {_≤_ = _≋_}

-- Associativity : ∀
--   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
--     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
--   {ℓ}
--     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
--   → Set (𝔞 ⊔ 𝔰 ⊔ ℓ)
-- Associativity {_►_ = _►_} _◅_ _≤_ =
--   ∀ {l} {m} {n} {w : m ► n} → Preservativity (λ ⋆ → _◅_ ⋆) (λ ⋆ → _◅_ ⋆) _≤_ (m ⟨ l ►_ ⟩→ n ∋ w ◅_) id (m ⟨ l ►_ ⟩→ n ∋ w ◅_)



-- -- record Associativity
-- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- --   {𝔱} {▸ : 𝔄 → Set 𝔱}
-- --     (_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n)
-- --   {ℓ}
-- --     (_≤_ : ∀ {n} → ▸ n → ▸ n → Set ℓ)
-- --   : Set (𝔞 ⊔ 𝔰 ⊔ 𝔱 ⊔ ℓ) where
-- --   field
-- --     associativity : ∀ {l} (f : ▸ l) {m} (g : l ► m) {n} (h : m ► n) → (h ◃ (g ◃ f)) ≤ ((h ◅ g) ◃ f)

-- -- open Associativity ⦃ … ⦄ public

-- -- -- record Associativity
-- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- --     (_▻_ : ∀ {l m n} → l ► m → m ⟨ _► n ⟩→ l)
-- -- --   {ℓ}
-- -- --     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
-- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
-- -- --   field
-- -- --     ⦃ `preservativity ⦄ : ∀ l m n w → Preservativity (_▻_ {l = l} {m = m} {n = n}) (_▻_ {l = l}) _≤_ (w ▻_) id (w ▻_)
-- -- -- --    ⦃ `preservativity ⦄ : ∀ n l w → Preservativity (λ ⋆ → _◅_ {n = n} ⋆) (λ ⋆ → _◅_ {l = l} ⋆) _≤_ (_◅ w) id (w ◅_)

-- -- -- -- record Associativity
-- -- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- -- --     (_◅_ : ∀ {l m n} → m ► n → m ⟨ l ►_ ⟩→ n)
-- -- -- --   {ℓ}
-- -- -- --     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
-- -- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
-- -- -- --   field
-- -- -- --     ⦃ `preservativity ⦄ : ∀ l n w → Preservativity (flip (_◅_ {l = l} {n = n})) (flip _◅_) _≤_ (w ◅_) id (_◅ w)
-- -- -- -- --    ⦃ `preservativity ⦄ : ∀ n l w → Preservativity (λ ⋆ → _◅_ {n = n} ⋆) (λ ⋆ → _◅_ {l = l} ⋆) _≤_ (_◅ w) id (w ◅_)

-- -- -- -- -- record Associativity
-- -- -- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- -- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- -- -- -- --   {ℓ}
-- -- -- -- --     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
-- -- -- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
-- -- -- -- --   field
-- -- -- -- --     ⦃ `preservativity ⦄ : ∀ n l w → Preservativity (λ ⋆ → _◅_ {n = n} ⋆) (λ ⋆ → _◅_ ⋆ {l = l}) _≤_ (_◅ w) id (w ◅_)

-- -- -- -- -- --    associativity : ∀ {k l} (f : k ► l) {m} (g : l ► m) {n} (h : m ► n) → (h ◅ (g ◅ f)) ≤ ((h ◅ g) ◅ f)

-- -- -- -- -- -- record Associativity
-- -- -- -- -- --   {a} {A : Set a} {b} {B : A → Set b} {c} {C : (x : A) → B x → Set c}
-- -- -- -- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- -- -- -- -- --   {ℓ}
-- -- -- -- -- --     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
-- -- -- -- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
-- -- -- -- -- --   field
-- -- -- -- -- --     ⦃ `preservativity ⦄ : Preservativity
-- -- -- -- -- --     associativity : ∀ {k l} (f : k ► l) {m} (g : l ► m) {n} (h : m ► n) → (h ◅ (g ◅ f)) ≤ ((h ◅ g) ◅ f)

-- -- -- -- -- -- open Associativity ⦃ … ⦄ public

-- -- -- -- -- -- -- record Associativity
-- -- -- -- -- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- -- -- -- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- -- -- -- -- -- --   {ℓ}
-- -- -- -- -- -- --     (_≤_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
-- -- -- -- -- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     associativity : ∀ {k l} (f : k ► l) {m} (g : l ► m) {n} (h : m ► n) → (h ◅ (g ◅ f)) ≤ ((h ◅ g) ◅ f)

-- -- -- -- -- -- -- open Associativity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- record Associativity
-- -- -- -- -- -- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- -- -- -- -- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- -- -- -- -- -- -- --   {𝔱} {▸ : 𝔄 → Set 𝔱}
-- -- -- -- -- -- -- --     (_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n)
-- -- -- -- -- -- -- --   {ℓ}
-- -- -- -- -- -- -- --     (_≤_ : ∀ {n} → ▸ n → ▸ n → Set ℓ)
-- -- -- -- -- -- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ 𝔱 ⊔ ℓ) where
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     associativity : ∀ {l} (f : ▸ l) {m} (g : l ► m) {n} (h : m ► n) → (h ◃ (g ◃ f)) ≤ ((h ◅ g) ◃ f)

-- -- -- -- -- -- -- -- open Associativity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- association : ∀
-- -- -- -- -- -- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- -- -- -- -- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
-- -- -- -- -- -- -- --   {𝔱} {▸ : 𝔄 → Set 𝔱}
-- -- -- -- -- -- -- --     {_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n}
-- -- -- -- -- -- -- --   {ℓ}
-- -- -- -- -- -- -- --     (_≤_ : ∀ {n} → ▸ n → ▸ n → Set ℓ)
-- -- -- -- -- -- -- --   ⦃ _ : Associativity _◅_ _◃_ _≤_ ⦄
-- -- -- -- -- -- -- --   → ∀ {l} (f : ▸ l) {m} (g : l ► m) {n} (h : m ► n) → (h ◃ (g ◃ f)) ≤ ((h ◅ g) ◃ f)
-- -- -- -- -- -- -- -- association _◅_ _≤_ = associativity {_◅_ = _◅_} {_≤_ = _≤_}
