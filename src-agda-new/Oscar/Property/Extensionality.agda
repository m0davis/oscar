
module Oscar.Property.Extensionality where

open import Oscar.Level

record Extensionality
  {a} {A : Set a} {b} {B : A → Set b} {ℓ₁}
    (_≤₁_ : (x : A) → B x → Set ℓ₁)
  {c} {C : A → Set c} {d} {D : ∀ {x} → B x → Set d} {ℓ₂}
    (_≤₂_ : ∀ {x} → C x → ∀ {y : B x} → D y → Set ℓ₂)
    (μ₁ : (x : A) → C x)
    (μ₂ : ∀ {x} → (y : B x) → D y)
  : Set (a ⊔ ℓ₁ ⊔ b ⊔ ℓ₂) where
  field
    extensionality : ∀ {x} {y : B x} → x ≤₁ y → μ₁ x ≤₂ μ₂ y

open Extensionality ⦃ … ⦄ public

extension : ∀
    {a} {A : Set a}
    {b} {B : A → Set b}
    {ℓ₁} {_≤₁_ : (x : A) → B x → Set ℓ₁}
    {c} {C : A → Set c} {d} {D : ∀ {x} → B x → Set d} {ℓ₂}
  (_≤₂_ : ∀ {x} → C x → ∀ {y : B x} → D y → Set ℓ₂)
    {μ₁ : (x : A) → C x}
    {μ₂ : ∀ {x} → (y : B x) → D y}
  ⦃ _ : Extensionality _≤₁_ _≤₂_ μ₁ μ₂ ⦄
    {x} {y : B x}
  → x ≤₁ y → μ₁ x ≤₂ μ₂ y
extension _≤₂_ = extensionality {_≤₂_ = _≤₂_}
