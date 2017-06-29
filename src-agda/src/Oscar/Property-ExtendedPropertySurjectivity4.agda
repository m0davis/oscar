{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity4 where

open import Oscar.Prelude using (_$_)


infixr 5 _,_
record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
  constructor _,_
  field
    π₀ : 𝔒
    π₁ : 𝔓 π₀

open Σ public


Extended :
    {𝔄 : Set}
    {𝔅 : Set}
    (_≈_ : 𝔅 → 𝔅 → Set)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Set
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

postulate 𝔛 : Set
postulate 𝔒 : 𝔛 → Set
-- postulate Arrow : 𝔛 → 𝔛 → Set

Arrow : 𝔛 → 𝔛 → Set
Arrow x y = 𝔒 x → 𝔒 y

module _
--  (_∼₁_ : 𝔛 → 𝔛 → Set)
  (_∼₂_ : 𝔛 → 𝔛 → Set₁)
  where
  record [𝓢urjectivity] : Set where
    no-eta-equality
  record 𝓢urjectivity ⦃ _ : [𝓢urjectivity] ⦄ : Set₁ where
    field
      surjectivity : ∀ {x y} → Arrow x y → x ∼₂ y

open 𝓢urjectivity ⦃ … ⦄ public

Property : ∀
  (𝔒 : 𝔛 → Set)
  → Set₁
Property 𝔒 = ∀ x → 𝔒 x → Set

ExtendedProperty : (y : 𝔛) (R : ∀ {x} → (Arrow y) x → (Arrow y) x → Set) → Set₁
ExtendedProperty y R = Σ (Property (Arrow y)) (λ P → ∀ x (f g : (Arrow y) x) → R f g → P _ f → P _ g)

ExtendedPropertyArrow : (x : 𝔛) (R : ∀ y → Arrow x y → Arrow x y → Set) → Set₁
ExtendedPropertyArrow x R = ExtendedProperty x (R _)

Extension : ∀ (𝔓 : 𝔛 → Set₁) → 𝔛 → 𝔛 → Set₁
Extension 𝔓 m n = 𝔓 m → 𝔓 n

ExtensionExtendedPropertyArrow : (x : 𝔛) (R : ∀ y → Arrow x y → Arrow x y → Set) → Set₁
ExtensionExtendedPropertyArrow x R = ExtendedProperty x (R _)

instance
  postulate
    ExtendedPropertySurjectivity : ∀
      {S : ∀ x → 𝔒 x → 𝔒 x → Set}
      ⦃ xi : [𝓢urjectivity] (λ m n →
          Σ ((x : 𝔛) → (𝔒 m → 𝔒 x) → Set)
          (λ P →
             (x : 𝔛) (f g : 𝔒 m → 𝔒 x) →
             ((x₁ : 𝔒 m) → S x (f x₁) (g x₁)) → P x f → P x g) →
          Σ ((x : 𝔛) → (𝔒 n → 𝔒 x) → Set)
          (λ P →
             (x : 𝔛) (f g : 𝔒 n → 𝔒 x) →
             ((x₁ : 𝔒 n) → S x (f x₁) (g x₁)) → P x f → P x g)) ⦄
      → 𝓢urjectivity (Extension $ λ v → ExtendedPropertyArrow v (λ w → Extended (S _)))

module _
  (R : ∀ x → 𝔒 x → 𝔒 x → Set)
  ⦃ xi : {![𝓢urjectivity] (Extension $ λ v → ExtendedPropertyArrow v (λ w f g → (x : 𝔒 v) → R w (f x) (g x)))!} ⦄
  where

  works : ∀ {x y} → Arrow x y → ExtendedPropertyArrow x (λ w f g → ∀ v → R w (f v) (g v)) → ExtendedPropertyArrow y (λ w f g → ∀ v → R w (f v) (g v))
  works {x} {y} f P =
    surjectivity
    {_∼₂_ = λ m n →
      Σ ((x₁ : 𝔛) → (𝔒 m → 𝔒 x₁) → Set)
        (λ P₁ →
          (x₁ : 𝔛) (f₁ g : 𝔒 m → 𝔒 x₁) →
          ((x₂ : 𝔒 m) → R x₁ (f₁ x₂) (g x₂)) → P₁ x₁ f₁ → P₁ x₁ g) →
      Σ ((x₁ : 𝔛) → (𝔒 n → 𝔒 x₁) → Set)
        (λ P₁ →
          (x₁ : 𝔛) (f₁ g : 𝔒 n → 𝔒 x₁) →
          ((x₂ : 𝔒 n) → R x₁ (f₁ x₂) (g x₂)) → P₁ x₁ f₁ → P₁ x₁ g)}
    ⦃ xi ⦄
    ⦃ ExtendedPropertySurjectivity {S = R} ⦄
    {x} {y} f $ P

  fails : ∀ {x y} → Arrow x y → ExtendedPropertyArrow x (λ w f g → ∀ v → R w (f v) (g v)) → ExtendedPropertyArrow y (λ w f g → ∀ v → R w (f v) (g v))
  fails {x} {y} f P =
    surjectivity
    {_∼₂_ = λ m n →
      Σ ((x₁ : 𝔛) → (𝔒 m → 𝔒 x₁) → Set)
        (λ P₁ →
          (x₁ : 𝔛) (f₁ g : 𝔒 m → 𝔒 x₁) →
          ((x₂ : 𝔒 m) → R x₁ (f₁ x₂) (g x₂)) → P₁ x₁ f₁ → P₁ x₁ g) →
      Σ ((x₁ : 𝔛) → (𝔒 n → 𝔒 x₁) → Set)
        (λ P₁ →
          (x₁ : 𝔛) (f₁ g : 𝔒 n → 𝔒 x₁) →
          ((x₂ : 𝔒 n) → R x₁ (f₁ x₂) (g x₂)) → P₁ x₁ f₁ → P₁ x₁ g)}
    ⦃ xi ⦄
    {x} {y} f $ P
