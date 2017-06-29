{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity7 where

postulate 𝔛 : Set
postulate 𝔒 : 𝔛 → Set

Arrow : 𝔛 → 𝔛 → Set
Arrow x y = 𝔒 x → 𝔒 y

Extended :
    (v w : 𝔛)
    (H : 𝔒 w → 𝔒 w → Set)
    → Arrow v w → Arrow v w
    → Set
Extended v w H = λ f g → ∀ l → H (f l) (g l)

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
      → 𝓢urjectivity (Extension (λ v → Property v (λ w → Extended v w (R w))))

module _
  (R : ∀ h → 𝔒 h → 𝔒 h → Set)
  where

  works : ∀ {x y} → Arrow x y → Extension (λ v → Property v (λ w → Extended v w (R w)))
  works = surjectivity ⦃ r = ExtendedPropertySurjectivity {R = R} ⦄

  fails : ∀ {j k} → Arrow j k → Extension (λ v → Property v (λ w → Extended v w (R w)))
  fails = surjectivity
