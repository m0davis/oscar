
module Oscar.Class.Semifunctor where

open import Oscar.Class.Semigroup
open import Oscar.Class.Extensionality
open import Oscar.Class.Preservativity
open import Oscar.Function
open import Oscar.Level
open import Oscar.Relation

record Semifunctor
  {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁}
    (_◅₁_ : ∀ {m n} → m ►₁ n → ∀ {l} → m ⟨ l ►₁_ ⟩→ n)
  {ℓ₁}
    (_≋₁_ : ∀ {m n} → m ►₁ n → m ►₁ n → Set ℓ₁)
  {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} {_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂}
    (_◅₂_ : ∀ {m n} → m ►₂ n → ∀ {l} → m ⟨ l ►₂_ ⟩→ n)
  {ℓ₂}
    (_≋₂_ : ∀ {m n} → m ►₂ n → m ►₂ n → Set ℓ₂)
  (μ : 𝔄₁ → 𝔄₂)
  (□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n)
  : Set (𝔞₁ ⊔ 𝔰₁ ⊔ ℓ₁ ⊔ 𝔞₂ ⊔ 𝔰₂ ⊔ ℓ₂) where
  field
    ⦃ ′semigroup₁ ⦄ : Semigroup _◅₁_ _≋₁_
    ⦃ ′semigroup₂ ⦄ : Semigroup _◅₂_ _≋₂_
    ⦃ ′extensionality ⦄ : ∀ {m n} → Extensionality (_≋₁_ {m} {n}) (λ ⋆ → _≋₂_ {μ m} {μ n} ⋆) □ □
    ⦃ ′preservativity ⦄ : ∀ {l m n} → Preservativity (λ ⋆ → _◅₁_ {m = m} {n = n} ⋆ {l = l}) (λ ⋆ → _◅₂_ ⋆) _≋₂_ □ □ □

instance

  Semifunctor⋆ : ∀
    {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁}
      {_◅₁_ : ∀ {m n} → m ►₁ n → ∀ {l} → m ⟨ l ►₁_ ⟩→ n}
    {ℓ₁}
      {_≋₁_ : ∀ {m n} → m ►₁ n → m ►₁ n → Set ℓ₁}
    {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} {_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂}
      {_◅₂_ : ∀ {m n} → m ►₂ n → ∀ {l} → m ⟨ l ►₂_ ⟩→ n}
    {ℓ₂}
      {_≋₂_ : ∀ {m n} → m ►₂ n → m ►₂ n → Set ℓ₂}
    {μ : 𝔄₁ → 𝔄₂}
    {□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n}
    ⦃ _ : Semigroup _◅₁_ _≋₁_ ⦄
    ⦃ _ : Semigroup _◅₂_ _≋₂_ ⦄
    ⦃ _ : ∀ {m n} → Extensionality (_≋₁_ {m} {n}) (λ ⋆ → _≋₂_ {μ m} {μ n} ⋆) □ □ ⦄
    ⦃ _ : ∀ {l m n} → Preservativity (λ ⋆ → _◅₁_ {m = m} {n = n} ⋆ {l = l}) (λ ⋆ → _◅₂_ ⋆) _≋₂_ □ □ □ ⦄
    → Semifunctor _◅₁_ _≋₁_ _◅₂_ _≋₂_ μ □
  Semifunctor.′semigroup₁ Semifunctor⋆ = it
  Semifunctor.′semigroup₂ Semifunctor⋆ = it
  Semifunctor.′extensionality Semifunctor⋆ = it
  Semifunctor.′preservativity Semifunctor⋆ = it

-- record Semifunctor'
--   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
--     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
--   {ℓ₁}
--     (_≋₁_ : ∀ {m n} → m ► n → m ► n → Set ℓ₁)
--   {𝔱} {▸ : 𝔄 → Set 𝔱}
--     (_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n)
--   {ℓ₂}
--     (_≋₂_ : ∀ {n} → ▸ n → ▸ n → Set ℓ₂)
--   (□ : ∀ {m n} → m ► n → m ► n)
--   : Set (𝔞 ⊔ 𝔰 ⊔ ℓ₁ ⊔ 𝔱 ⊔ ℓ₂) where
--   field
--     ⦃ ′semigroup₁ ⦄ : Semigroup _◅_ (λ ⋆ → _◅_ ⋆) _≋₁_
--     ⦃ ′semigroup₂ ⦄ : Semigroup _◅_ _◃_ _≋₂_
--     ⦃ ′extensionality ⦄ : ∀ {m} {t : ▸ m} {n} → Extensionality (_≋₁_ {m} {n}) (λ ⋆ → _≋₂_ {n} ⋆) (_◃ t) (_◃ t)
--     ⦃ ′preservativity ⦄ : Preservativity _►₁_ _◃₁_ _►₂_ _◃₂_ _≋₂_ ◽ □

-- record Semifunctor
--   {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁}
--     (_◅₁_ : ∀ {m n} → m ►₁ n → ∀ {l} → m ⟨ l ►₁_ ⟩→ n)
--   {𝔱₁} {▸₁ : 𝔄₁ → Set 𝔱₁}
--     (_◃₁_ : ∀ {m n} → m ►₁ n → m ⟨ ▸₁ ⟩→ n)
--   {ℓ₁}
--     (_≋₁_ : ∀ {n} → ▸₁ n → ▸₁ n → Set ℓ₁)
--   {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} {_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂}
--     (_◅₂_ : ∀ {m n} → m ►₂ n → ∀ {l} → m ⟨ l ►₂_ ⟩→ n)
--   {𝔱₂} {▸₂ : 𝔄₂ → Set 𝔱₂}
--     (_◃₂_ : ∀ {m n} → m ►₂ n → m ⟨ ▸₂ ⟩→ n)
--   {ℓ₂}
--     (_≋₂_ : ∀ {n} → ▸₂ n → ▸₂ n → Set ℓ₂)
--   (μ : 𝔄₁ → 𝔄₂)
--   (◽ : ∀ {n} → ▸₁ n → ▸₂ (μ n))
--   (□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n)
--   : Set (𝔞₁ ⊔ 𝔰₁ ⊔ 𝔱₁ ⊔ ℓ₁ ⊔ 𝔞₂ ⊔ 𝔰₂ ⊔ 𝔱₂ ⊔ ℓ₂) where
--   field
--     ⦃ ′semigroup₁ ⦄ : Semigroup _◅₁_ _◃₁_ _≋₁_
--     ⦃ ′semigroup₂ ⦄ : Semigroup _◅₂_ _◃₂_ _≋₂_
--     ⦃ ′extensionality ⦄ : ∀ {n} → Extensionality (_≋₁_ {n}) (λ ⋆ → _≋₂_ {μ n} ⋆) ◽ ◽
--     ⦃ ′preservativity ⦄ : Preservativity _►₁_ _◃₁_ _►₂_ _◃₂_ _≋₂_ ◽ □

-- open Semifunctor ⦃ … ⦄ public hiding (′semigroup₁; ′semigroup₂; ′extensionality; ′preservativity)

-- instance

--   Semifunctor⋆ : ∀
--     {𝔞₁} {𝔄₁ : Set 𝔞₁} {𝔰₁} {_►₁_ : 𝔄₁ → 𝔄₁ → Set 𝔰₁}
--       {_◅₁_ : ∀ {m n} → m ►₁ n → ∀ {l} → m ⟨ l ►₁_ ⟩→ n}
--     {𝔱₁} {▸₁ : 𝔄₁ → Set 𝔱₁}
--       {_◃₁_ : ∀ {m n} → m ►₁ n → m ⟨ ▸₁ ⟩→ n}
--     {ℓ₁}
--       {_≋₁_ : ∀ {n} → ▸₁ n → ▸₁ n → Set ℓ₁}
--     {𝔞₂} {𝔄₂ : Set 𝔞₂} {𝔰₂} {_►₂_ : 𝔄₂ → 𝔄₂ → Set 𝔰₂}
--       {_◅₂_ : ∀ {m n} → m ►₂ n → ∀ {l} → m ⟨ l ►₂_ ⟩→ n}
--     {𝔱₂} {▸₂ : 𝔄₂ → Set 𝔱₂}
--       {_◃₂_ : ∀ {m n} → m ►₂ n → m ⟨ ▸₂ ⟩→ n}
--     {ℓ₂}
--       {_≋₂_ : ∀ {n} → ▸₂ n → ▸₂ n → Set ℓ₂}
--     {μ : 𝔄₁ → 𝔄₂}
--     {◽ : ∀ {n} → ▸₁ n → ▸₂ (μ n)}
--     {□ : ∀ {m n} → m ►₁ n → μ m ►₂ μ n}
--     ⦃ _ : Semigroup _◅₁_ _◃₁_ _≋₁_ ⦄
--     ⦃ _ : Semigroup _◅₂_ _◃₂_ _≋₂_ ⦄
--     ⦃ _ : ∀ {n} → Extensionality (_≋₁_ {n}) (λ ⋆ → _≋₂_ {μ n} ⋆) ◽ ◽ ⦄
--     ⦃ _ : Preservativity _►₁_ _◃₁_ _►₂_ _◃₂_ _≋₂_ ◽ □ ⦄
--     → Semifunctor _◅₁_ _◃₁_ _≋₁_ _◅₂_ _◃₂_ _≋₂_ μ ◽ □
--   Semifunctor.′semigroup₁ Semifunctor⋆ = it
--   Semifunctor.′semigroup₂ Semifunctor⋆ = it
--   Semifunctor.′extensionality Semifunctor⋆ = it
--   Semifunctor.′preservativity Semifunctor⋆ = it
