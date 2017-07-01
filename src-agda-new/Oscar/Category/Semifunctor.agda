
module Oscar.Category.Semifunctor where

open import Oscar.Category.Setoid
open import Oscar.Category.Semigroupoid
open import Oscar.Level

module _
  {𝔬₁ 𝔪₁ 𝔮₁} (semigroupoid₁ : Semigroupoid 𝔬₁ 𝔪₁ 𝔮₁)
  {𝔬₂ 𝔪₂ 𝔮₂} (semigroupoid₂ : Semigroupoid 𝔬₂ 𝔪₂ 𝔮₂)
  where

  private module 𝔊₁ = Semigroupoid semigroupoid₁
  private module 𝔊₂ = Semigroupoid semigroupoid₂

--   record IsSemifunctor
--     (μ : 𝔊₁.⋆ → 𝔊₂.⋆)
--     (𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y)
--     : Set (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂) where
--     field
--       extensionality : ∀ {x y} {f₁ f₂ : x 𝔊₁.↦ y} → f₁ ≋ f₂ → 𝔣 f₁ ≋ 𝔣 f₂
--       distributivity : ∀ {x y} (f : x 𝔊₁.↦ y) {z} (g : y 𝔊₁.↦ z) → 𝔣 (g 𝔊₁.∙ f) ≋ 𝔣 g 𝔊₂.∙ 𝔣 f

-- open IsSemifunctor ⦃ … ⦄ public

-- record Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
--   field
--     semigroupoid₁ : Semigroupoid 𝔬₁ 𝔪₁ 𝔮₁
--     semigroupoid₂ : Semigroupoid 𝔬₂ 𝔪₂ 𝔮₂

--   module 𝔊₁ = Semigroupoid semigroupoid₁
--   module 𝔊₂ = Semigroupoid semigroupoid₂

--   field
--     μ : 𝔊₁.⋆ → 𝔊₂.⋆
--     𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y
--     ⦃ isSemifunctor ⦄ : IsSemifunctor semigroupoid₁ semigroupoid₂ μ 𝔣



-- record Semigroupoids 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
--   constructor _,_
--   field
--     semigroupoid₁ : Semigroupoid 𝔬₁ 𝔪₁ 𝔮₁
--     semigroupoid₂ : Semigroupoid 𝔬₂ 𝔪₂ 𝔮₂

--   module 𝔊₁ = Semigroupoid semigroupoid₁
--   module 𝔊₂ = Semigroupoid semigroupoid₂

-- module _
--   {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂} (semigroupoids : Semigroupoids 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂)
--   where
--   open Semigroupoids semigroupoids
--   record IsSemifunctor
--     {μ : 𝔊₁.⋆ → 𝔊₂.⋆}
--     (𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y)
--     : Set (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂) where
--     instance _ = 𝔊₁.IsSetoid↦
--     instance _ = 𝔊₂.IsSetoid↦
--     field
--       extensionality : ∀ {x y} {f₁ f₂ : x 𝔊₁.↦ y} → f₁ ≋ f₂ → 𝔣 f₁ ≋ 𝔣 f₂
--       distributivity : ∀ {x y} (f : x 𝔊₁.↦ y) {z} (g : y 𝔊₁.↦ z) → 𝔣 (g 𝔊₁.∙ f) ≋ 𝔣 g 𝔊₂.∙ 𝔣 f

-- open IsSemifunctor ⦃ … ⦄ public

-- record Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Set (lsuc (𝔬₁ ⊔ 𝔪₁ ⊔ 𝔮₁ ⊔ 𝔬₂ ⊔ 𝔪₂ ⊔ 𝔮₂)) where
--   constructor _,_
--   field
--     semigroupoids : Semigroupoids 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂

--   open Semigroupoids semigroupoids public

--   field
--     {μ} : 𝔊₁.⋆ → 𝔊₂.⋆
--     𝔣 : ∀ {x y} → x 𝔊₁.↦ y → μ x 𝔊₂.↦ μ y
--     ⦃ isSemifunctor ⦄ : IsSemifunctor semigroupoids 𝔣
--   open IsSemifunctor isSemifunctor public
