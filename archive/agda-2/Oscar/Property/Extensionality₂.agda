
module Oscar.Property.Extensionality₂ where

open import Oscar.Level

record Extensionality₂
  {a} {A : Set a} {b} {B : A → Set b} {ℓ₁}
    (_≤₁_ : (w : A) → B w → Set ℓ₁)
  {c} {C : ∀ {w} → B w → Set c} {d} {D : ∀ {w} {x : B w} → C x → Set d} {ℓ₂}
    (_≤₂_ : ∀ {w} {x : B w} → (y : C x) → D y → Set ℓ₂)
  {e} {E : ∀ {w} {y : B w} → C y → Set e} {f} {F : ∀ {w} {x : B w} {y : C x} → D y → Set f}
    (μ₁ : ∀ {w} {x : B w} → (y : C x) → E y)
    (μ₂ : ∀ {w} {x : B w} {y : C x} → (z : D y) → F z)
  {ℓ₃}
    (_≤₃_ : ∀ {w} {x : B w} {y : C x} → E y → ∀ {z : D y} → F z → Set ℓ₃)
  : Set (a ⊔ b ⊔ ℓ₁ ⊔ c ⊔ d ⊔ ℓ₂ ⊔ e ⊔ f ⊔ ℓ₃) where
  field
    extensionality₂ : ∀ {w} {x : B w} → w ≤₁ x → ∀ {y : C x} {z : D y} → y ≤₂ z → μ₁ y ≤₃ μ₂ z

open Extensionality₂ ⦃ … ⦄ public

extension₂ : ∀
  {a} {A : Set a} {b} {B : A → Set b} {ℓ₁}
    {_≤₁_ : (w : A) → B w → Set ℓ₁}
  {c} {C : ∀ {w} → B w → Set c} {d} {D : ∀ {w} {x : B w} → C x → Set d} {ℓ₂}
    {_≤₂_ : ∀ {w} {x : B w} → (y : C x) → D y → Set ℓ₂}
  {e} {E : ∀ {w} {y : B w} → C y → Set e} {f} {F : ∀ {w} {x : B w} {y : C x} → D y → Set f} {ℓ₃}
    (_≤₃_ : ∀ {w} {x : B w} {y : C x} → E y → ∀ {z : D y} → F z → Set ℓ₃)
    {μ₁ : ∀ {w} {x : B w} → (y : C x) → E y}
    {μ₂ : ∀ {w} {x : B w} {y : C x} → (z : D y) → F z}
  ⦃ _ : Extensionality₂ _≤₁_ _≤₂_ μ₁ μ₂ _≤₃_ ⦄
    {w} {x : B w}
  → w ≤₁ x
  → ∀ {y : C x} {z : D y}
  → y ≤₂ z
  → μ₁ y ≤₃ μ₂ z
extension₂ _≤₃_ = extensionality₂ {_≤₃_ = _≤₃_}

record Extensionality₂⋆
  {yz} {YZ : Set yz}
  {ℓ₁}
    (_≤₁_ : YZ → YZ → Set ℓ₁)
  {xy} {XY : Set xy}
  {ℓ₂}
    (_≤₂_ : XY → XY → Set ℓ₂)
  {xz} {XZ : Set xz}
  {ℓ₃}
    (_≤₃_ : XZ → XZ → Set ℓ₃)
  (μ₁ : YZ → XY → XZ)
  (μ₂ : YZ → XY → XZ)
  : Set (yz ⊔ ℓ₁ ⊔ xy ⊔ ℓ₂ ⊔ xz ⊔ ℓ₃) where
  field
    extensionality* : ∀ {g₁ g₂ : YZ} → g₁ ≤₁ g₂ → ∀ {f₁ f₂ : XY} → f₁ ≤₂ f₂ → μ₁ g₁ f₁ ≤₃ μ₂ g₂ f₂
--  extensionality* : ∀ {y z} {g₁ g₂ : y ⇒ z} → g₁ ≤₁ g₂ → ∀ {x} {f₁ f₂ : x ⇒ y} → f₁ ≤₂ f₂ → μ₁ g₁ f₁ ≤₃ μ₂ g₂ f₂

open Extensionality₂⋆ ⦃ … ⦄ public

instance

  toExt : ∀
    {yz} {YZ : Set yz}
    {ℓ₁}
      {_≤₁_ : YZ → YZ → Set ℓ₁}
    {xy} {XY : Set xy}
    {ℓ₂}
      {_≤₂_ : XY → XY → Set ℓ₂}
    {xz} {XZ : Set xz}
    {ℓ₃}
      {_≤₃_ : XZ → XZ → Set ℓ₃}
    {μ₁ : YZ → XY → XZ}
    {μ₂ : YZ → XY → XZ}
    ⦃ _ : Extensionality₂⋆ _≤₁_ _≤₂_ _≤₃_ μ₁ μ₂ ⦄
    → Extensionality₂ _≤₁_ _≤₂_ (λ {w} y → μ₁ w y) (λ {_} {x} z → μ₂ x z) (λ ‵ → _≤₃_ ‵)
  Extensionality₂.extensionality₂ (toExt {yz} {YZ} {ℓ₁} {_≤₁_} {xy} {XY} {ℓ₂} {_≤₂_} {xz} {XZ} {ℓ₃} {_≤₃_} {μ₁} {μ₂} {{x}}) = extensionality* ⦃ x ⦄
