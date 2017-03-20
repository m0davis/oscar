
module Oscar.Category.Functor where

open import Oscar.Category.Setoid
open import Oscar.Category.Category
open import Oscar.Category.Semifunctor
open import Oscar.Level

record Categories 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
  constructor _,_
  field
    category₁ : Category 𝔬₁ 𝔪₁ 𝔮₁
    category₂ : Category 𝔬₂ 𝔪₂ 𝔮₂

  module 𝔊₁ = Category category₁
  module 𝔊₂ = Category category₂

  semigroupoids : Semigroupoids _ _ _ _ _ _
  Semigroupoids.semigroupoid₁ semigroupoids = 𝔊₁.semigroupoid
  Semigroupoids.semigroupoid₂ semigroupoids = 𝔊₂.semigroupoid

module _
  {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂} (categories : Categories 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂)
  where
  open Categories categories

  record IsFunctor
    {μ : 𝔊₁.⋆ → 𝔊₂.⋆}
    (𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y)
    : Set (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂) where
    field
      ⦃ isSemifunctor ⦄ : IsSemifunctor semigroupoids 𝔣
    field
      identity : (x : 𝔊₁.⋆) → 𝔣 (𝔊₁.ε {x = x}) ≋ 𝔊₂.ε
    open IsSemifunctor isSemifunctor public

open IsFunctor ⦃ … ⦄ public

open import Oscar.Category.Morphism

record Functor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
  constructor _,_
  field
    categories : Categories 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂
  open Categories categories public

  field
    {μ} : 𝔊₁.⋆ → 𝔊₂.⋆
    𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y
    ⦃ isFunctor ⦄ : IsFunctor categories 𝔣
  open IsFunctor isFunctor public

-- module _
--   {𝔬₁ 𝔪₁ 𝔮₁} (category₁ : Category 𝔬₁ 𝔪₁ 𝔮₁)
--   {𝔬₂ 𝔪₂ 𝔮₂} (category₂ : Category 𝔬₂ 𝔪₂ 𝔮₂)
--   where

--   private module 𝔊₁ = Category category₁
--   private module 𝔊₂ = Category category₂

--   record IsFunctor
--     (μ : 𝔊₁.⋆ → 𝔊₂.⋆)
--     (𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y)
--     : Set (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂) where
--     field
--       ⦃ isSemifunctor ⦄ : IsSemifunctor 𝔊₁.semigroupoid 𝔊₂.semigroupoid μ 𝔣
--     field
--       identity : (x : 𝔊₁.⋆) → 𝔣 (𝔊₁.ε {x = x}) ≋ 𝔊₂.ε

-- open IsFunctor ⦃ … ⦄ public

-- record Functor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
--   field
--     category₁ : Category 𝔬₁ 𝔪₁ 𝔮₁
--     category₂ : Category 𝔬₂ 𝔪₂ 𝔮₂

--   module 𝔊₁ = Category category₁
--   module 𝔊₂ = Category category₂

--   field
--     μ : 𝔊₁.⋆ → 𝔊₂.⋆
--     𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y
--     ⦃ isFunctor ⦄ : IsFunctor category₁ category₂ μ 𝔣
