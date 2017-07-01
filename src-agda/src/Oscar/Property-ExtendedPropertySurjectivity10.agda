
module Oscar.Property-ExtendedPropertySurjectivity10 where

postulate 𝔛 : Set
postulate y : 𝔛

Arrow : Set
Arrow = 𝔛 → 𝔛

Extended : (𝔛 → Set) → Set
Extended H = H y

postulate Property : Set → Set₁

PropertyExtended : (𝔛 → Set) → Set₁
PropertyExtended H = Property (Extended H)

record Surjectivity (T : Set₁) : Set₁ where
  field
    surjectivity : Arrow → T

open Surjectivity ⦃ … ⦄ public

instance
  postulate
    ExtendedPropertySurjectivity : {R : 𝔛 → Set} → Surjectivity (PropertyExtended R)

module _
  (R : 𝔛 → Set)
  where

  works : Arrow → PropertyExtended R
  works = surjectivity ⦃ ExtendedPropertySurjectivity {R = R} ⦄

  fails : Arrow → PropertyExtended R
  fails = surjectivity
