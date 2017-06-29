{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity5 where

Extended :
    {𝔄 : Set}
    {𝔅 : Set}
    (_≈_ : 𝔅 → 𝔅 → Set)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Set
Extended _≈_ = λ f g → ∀ l → f l ≈ g l

postulate 𝔛 : Set
postulate 𝔒 : 𝔛 → Set

Arrow : 𝔛 → 𝔛 → Set
Arrow x y = 𝔒 x → 𝔒 y

module _
  (T : 𝔛 → 𝔛 → Set₁)
  where
  record 𝓢urjectivity : Set₁ where
    field
      surjectivity : ∀ {i o} → Arrow i o → T i o

open 𝓢urjectivity ⦃ … ⦄ public

postulate Property : (b : 𝔛) (R : ∀ y → Arrow b y → Arrow b y → Set) → Set₁
postulate Extension : ∀ (𝔓 : 𝔛 → Set₁) → 𝔛 → 𝔛 → Set₁

instance
  postulate
    ExtendedPropertySurjectivity :
      {R : ∀ d → 𝔒 d → 𝔒 d → Set}
      → 𝓢urjectivity (Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w))))

module _
  (R : ∀ h → 𝔒 h → 𝔒 h → Set)
  where

  works : ∀ {x y} → Arrow x y → (Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w)))) x y
  works = surjectivity ⦃ r = ExtendedPropertySurjectivity {R = R} ⦄

  fails : ∀ {j k} → Arrow j k → (Extension (λ v → Property v (λ w → Extended {𝔄 = 𝔒 v} {𝔅 = 𝔒 w} (R w)))) j k
  fails = surjectivity
