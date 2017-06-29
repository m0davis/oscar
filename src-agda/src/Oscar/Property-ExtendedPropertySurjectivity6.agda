{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity6 where

postulate 𝔛 : Set
postulate 𝔒 : 𝔛 → Set

Extended :
    {𝔄 : Set}
    {𝔅 : Set}
    (_≈_ : 𝔅 → 𝔅 → Set)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Set
Extended _≈_ = λ f g → ∀ l → f l ≈ g l

Arrow : 𝔛 → 𝔛 → Set
Arrow x y = 𝔒 x → 𝔒 y

postulate Property : (b : 𝔛) (R : ∀ y → Arrow b y → Arrow b y → Set) → Set₁
postulate Extension : ∀ (𝔓 : 𝔛 → Set₁) → Set₁

record 𝓢urjectivity (T : Set₁) : Set₁ where
  field
    surjectivity : ∀ {i o} → Arrow i o → T

open 𝓢urjectivity ⦃ … ⦄ public

instance
  postulate
    ExtendedPropertySurjectivity :
      {R : ∀ d → 𝔒 d → 𝔒 d → Set}
      → 𝓢urjectivity (Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w))))

module _
  (R : ∀ h → 𝔒 h → 𝔒 h → Set)
  where

  works : ∀ {x y} → Arrow x y → Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w)))
  works = surjectivity ⦃ r = ExtendedPropertySurjectivity {R = R} ⦄

  fails : ∀ {j k} → Arrow j k → Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w)))
  fails = surjectivity
