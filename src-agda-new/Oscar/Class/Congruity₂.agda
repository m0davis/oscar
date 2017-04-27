
module Oscar.Class.Congruity₂ where

open import Oscar.Class.Extensionality
open import Oscar.Level

record Congruity₂
  {a} {A : Set a} {ℓ₁}
    (_≤₁_ : A → A → Set ℓ₁)
  {b} {B : A → Set b} {ℓ₂}
    (_≤₂_ : ∀ {x₁} → B x₁ → ∀ {x₂} → B x₂ → Set ℓ₂)
  {c} {C : ∀ {x} → B x → Set c} {ℓ₃}
    (_≤₃_ : ∀ {x₁} {y₁ : B x₁} → C y₁ → ∀ {x₂} {y₂ : B x₂} → C y₂ → Set ℓ₃)

       : Set (a ⊔ ℓ₁ ⊔ b ⊔ ℓ₂ ⊔ c ⊔ ℓ₃) where
  field
    congruity₂ : ∀ (μ : (x : A) → (y : B x) → C y) {w v} → w ≤₁ v → ∀ {x : B w} {y : B v} → x ≤₂ y → μ w x ≤₃ μ v y

--  instance ′extensionality : ∀ (μ : A → B) → Extensionality _≋₁_ (λ ⋆ → _≋₂_ ⋆) μ μ
--  Extensionality.extensionality (′extensionality μ) = congruity μ

open Congruity₂ ⦃ … ⦄ public -- hiding (′extensionality)
