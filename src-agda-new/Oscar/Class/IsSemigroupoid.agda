
module Oscar.Class.IsSemigroupoid where

open import Oscar.Class.Associativity
open import Oscar.Class.Equivalence
open import Oscar.Class.Extensionality₂
open import Oscar.Function
open import Oscar.Level
open import Oscar.Relation

record Semigroup
  {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
    (_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n)
  {ℓ}
    (_≋_ : ∀ {m n} → m ► n → m ► n → Set ℓ)
  : Set (𝔞 ⊔ 𝔰 ⊔ ℓ) where
  field
    ⦃ ′equivalence ⦄ : ∀ {m n} → Equivalence (_≋_ {m} {n})
    ⦃ ′associativity ⦄ : Associativity _◅_ _≋_
    ⦃ ′extensionality₂ ⦄ : ∀ {l m n} →
      Extensionality₂
        (_≋_ {m} {n})
        (_≋_ {l})
        (λ ⋆ → _≋_ ⋆)
        (λ ⋆ → _◅_ ⋆)
        (λ ⋆ → _◅_ ⋆)

open Semigroup ⦃ … ⦄ public hiding (′equivalence; ′associativity)

-- instance

--   Semigroup⋆ : ∀
--     {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
--       {_◅_ : ∀ {m n} → m ► n → ∀ {l} → m ⟨ l ►_ ⟩→ n}
--     {ℓ}
--       {_≋_ : ∀ {m n} → m ► n → m ► n → Set ℓ}
--     ⦃ _ : ∀ {m n} → Equivalence (_≋_ {m} {n}) ⦄
--     ⦃ _ : Associativity _◅_ _≋_ ⦄
--     → Semigroup _◅_ _≋_
--   Semigroup.′equivalence Semigroup⋆ = it
--   Semigroup.′associativity Semigroup⋆ = it

-- -- -- record Semigroup
-- -- --   {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- --     (_◅_ : ∀ {m n} → m ► n → ∀ {l} → l ► m → l ► n)
-- -- --   {𝔱} {▸ : 𝔄 → Set 𝔱}
-- -- --     (_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n)
-- -- --   {ℓ}
-- -- --     (_≋_ : ∀ {n} → ▸ n → ▸ n → Set ℓ)
-- -- --   : Set (𝔞 ⊔ 𝔰 ⊔ 𝔱 ⊔ ℓ) where
-- -- --   field
-- -- --     ⦃ ′equivalence ⦄ : ∀ {n} → Equivalence (_≋_ {n})
-- -- --     ⦃ ′associativity ⦄ : Associativity _◅_ _◃_ _≋_

-- -- -- open Semigroup ⦃ … ⦄ public hiding (′equivalence; ′associativity)

-- -- -- instance
-- -- --   Semigroup⋆ : ∀
-- -- --     {𝔞} {𝔄 : Set 𝔞} {𝔰} {_►_ : 𝔄 → 𝔄 → Set 𝔰}
-- -- --       {_◅_ : ∀ {m n} → m ► n → ∀ {l} → l ► m → l ► n}
-- -- --     {𝔱} {▸ : 𝔄 → Set 𝔱}
-- -- --       {_◃_ : ∀ {m n} → m ► n → m ⟨ ▸ ⟩→ n}
-- -- --     {ℓ}
-- -- --       {_≋_ : ∀ {n} → ▸ n → ▸ n → Set ℓ}
-- -- --     ⦃ _ : ∀ {n} → Equivalence (_≋_ {n}) ⦄
-- -- --     ⦃ _ : Associativity _◅_ _◃_ _≋_ ⦄
-- -- --     → Semigroup _◅_ _◃_ _≋_
-- -- --   Semigroup.′equivalence Semigroup⋆ = it
-- -- --   Semigroup.′associativity Semigroup⋆ = it
