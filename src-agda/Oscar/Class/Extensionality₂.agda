
module Oscar.Class.Extensionality₂ where

open import Oscar.Level

record Extensionality₂
  {a} {A : Set a}
  {b} {B : A → Set b}
  {ℓ₁}
    (_≤₁_ : (w : A) → B w → Set ℓ₁)
  {c} {C : ∀ {w : A} → B w → Set c }
  {d} {D : ∀ {w : A} {x : B w} → C x → Set d}
  {ℓ₂}
    (_≤₂_ : {w : A} {x : B w} → (y : C x) → D y → Set ℓ₂)
  {e} {E : ∀ {w} {x : B w} → C x → Set e}
  {f} {F : ∀ {w} {x : B w} {y : C x} → D y → Set f}
  {ℓ₃}
    (_≤₃_ : ∀ {w} {x : B w} {y : C x} → E y → ∀ {z : D y} → F z → Set ℓ₃)
    (μ₁ : (w : A) → ∀ {x : B w} → (y : C x) → E y)
    (μ₂ : ∀ {w : A} → (x : B w) → ∀ {y : C x} → (z : D y) → F z)
  : Set (a ⊔ b ⊔ ℓ₁ ⊔ c ⊔ d ⊔ ℓ₂ ⊔ e ⊔ f ⊔ ℓ₃) where
  field
    extensionality₂ : ∀
      {w : A} {x : B w}
      → w ≤₁ x
      → ∀ {y : C x} {z : D y}
      → y ≤₂ z
      → μ₁ w y ≤₃ μ₂ x z
--    extensionality₂ : ∀ {z : A} {y : B z} → z ≤₁ y → ∀ {x : A} {w : D x} → x ≤₂ w → μ₁ z x ≤₃ μ₂ y w

-- record Extensionality₂
--   {a} {A : Set a}
--   {b} {B : A → Set b}
--   {ℓ₁}
--     (_≤₁_ : (x : A) → B x → Set ℓ₁)
--   {c} {C : ∀ {x} → B x → Set c}
--   {d} {D : ∀ {x} {y : B x} → C y → Set d}
--   {ℓ₂}
--     (_≤₂_ : ∀ {x} {y : B x} → (z : C y)
--           → D z
--           → Set ℓ₂)
--   {e} {E : ∀ {x} {y : B x} → C y → Set e}
--   {f} {F : ∀ {x} {y : B x} {z : C y} → D z → E z → Set f}
--   {ℓ₃}
--     (_≤₃_ : ∀ {x} {y : B x} {z : C y} → (w : E z)
--           → ∀ {v : D z} → F v w
--           → Set ℓ₃)
--     (μ₁ : (x : A) → ∀ {y : B x} → (z : C y) → E z)
--     (μ₂ : ∀ {x} → (y : B x) → ∀ {z : C y} → (w : D y) → F w)
--   : Set (a ⊔ b ⊔ ℓ₁ ⊔ c ⊔ d ⊔ ℓ₂ ⊔ e ⊔ f ⊔ ℓ₃) where
--   field
--     extensionality₂ : ∀ {z : A} {y : B z} → z ≤₁ y → ∀ {x : A} {w : D x} → x ≤₂ w → μ₁ z x ≤₃ μ₂ y w
-- --    extensionality₂ : ∀ {z : A} {y : B z} → z ≤₁ y → ∀ {x : A} {w : D x} → x ≤₂ w → μ₁ z x ≤₃ μ₂ y w

-- open Extensionality₂ ⦃ … ⦄ public

-- {-
--   {a} {A : Set a} {b} {B : A → Set b} {ℓ₁}
--     (_≤₁_ : (x : A) → B x → Set ℓ₁)
--   {c} {C : A → Set c} {d} {D : ∀ {x} → B x → Set d} {ℓ₂}
--     (_≤₂_ : ∀ {x₁} → C x₁ → ∀ {x₂} {y : B x₂} → D y → Set ℓ₂)
-- -}
