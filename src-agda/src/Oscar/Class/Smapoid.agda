
open import Oscar.Class.Similarity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjection
open import Oscar.Class.Leftunit
open import Oscar.Class.Smap
open import Oscar.Class.Symmetrical
open import Oscar.Class.Unit
open import Oscar.Data.Surjcollation
open import Oscar.Prelude

module Oscar.Class.Smapoid where

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭₁} (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  {𝔭₂} (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇₁₁} (𝔓̇₁₁ : ∀ {x} → 𝔓₁ x → 𝔓₁ x → Ø 𝔭̇₁₁)
  {𝔭̇₂₂} (𝔓̇₂₂ : ∀ {x} → 𝔓₂ x → 𝔓₂ x → Ø 𝔭̇₂₂)
  {𝔭̇₁₂} (𝔓̇₁₂ : ∀ {x} → 𝔓₁ x → 𝔓₂ x → Ø 𝔭̇₁₂)
  where
  record IsSmapoid : Ø 𝔵₁ ∙̂ 𝔵₂ ∙̂ 𝔯 ∙̂ 𝔯̇ ∙̂ 𝔭₁ ∙̂ 𝔭₂ ∙̂ 𝔭̇₁₁ ∙̂ 𝔭̇₂₂ ∙̂ 𝔭̇₁₂ where
    constructor ∁
    field

      ⦃ `Surjection ⦄ : Surjection.class 𝔛₁ 𝔛₂

      -- ℜ 𝓂 𝓃 → 𝔓₁ (surjection 𝓂) → 𝔓₂ (surjection 𝓃)
      ⦃ `Smaparrow ⦄ : Smaparrow.class ℜ 𝔓₁ 𝔓₂ surjection -- epfs, Smap

      -- 𝒫 ₁≈₁ 𝒬 → 𝒻 ◃ 𝒫 ₂≈₂ 𝒻 ◃ 𝒬
      ⦃ `leftSim ⦄ : Similarity,smaparrow!.class ℜ 𝔓₁ 𝔓₂ 𝔓̇₁₁ 𝔓̇₂₂ -- fact5, Similarity, Smaparrowleftsimilarity



      ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity ℜ

      -- 𝒫 ₁≈₂ 𝒖 ◃ 𝒫
      ⦃ `leftyunit ⦄ : ∀ {x} {p : 𝔓₁ (surjection x)}
                     → Leftunit.class (flip (𝔓̇₁₂ {surjection x})) ε smap p

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭₁} (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  {𝔭₂} (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇₁₁} (𝔓̇₁₁ : ∀ {x} → 𝔓₁ x → 𝔓₁ x → Ø 𝔭̇₁₁)
  {𝔭̇₂₂} (𝔓̇₂₂ : ∀ {x} → 𝔓₂ x → 𝔓₂ x → Ø 𝔭̇₂₂)
  {𝔭̇₁₂} (𝔓̇₁₂ : ∀ {x} → 𝔓₁ x → 𝔓₂ x → Ø 𝔭̇₁₂)
  where
  record IsSmapoidR : Ø 𝔵₁ ∙̂ 𝔵₂ ∙̂ 𝔯 ∙̂ 𝔯̇ ∙̂ 𝔭₁ ∙̂ 𝔭₂ ∙̂ 𝔭̇₁₁ ∙̂ 𝔭̇₂₂ ∙̂ 𝔭̇₁₂ where
    constructor ∁
    field

      ⦃ `IsSmapoid ⦄ : IsSmapoid ℜ 𝔓₁ 𝔓₂ ℜ̇ 𝔓̇₁₁ 𝔓̇₂₂ 𝔓̇₁₂

      -- 𝒻 ᵣ≈ᵣ ℊ → 𝒻 ◃ 𝒫 ₂≈₂ ℊ ◃ 𝒫
      ⦃ `rightSim ⦄ : Similarity,cosmaparrow!.class ℜ 𝔓₁ 𝔓₂ ℜ̇ 𝔓̇₂₂ -- fact6, Similarity, Smaparrowrightsimilarity

-- TODO add these somewhere?
-- fact4 needs Propergroup's Nothing -- ⦃ `Leftstar ⦄ : Leftstar.class
-- left-identity-∧ needs Propergroup
-- fact1 -- ⦃ `Symmetrical ⦄ : ∀ {m} → Symmetrical (surjcollation[ 𝔓 ]⟦ ℜ / 𝔓̇ ⟧ {m}) (λ { (∁ f) (∁ g) → {!f {m}!}})
-- Properties-fact1
