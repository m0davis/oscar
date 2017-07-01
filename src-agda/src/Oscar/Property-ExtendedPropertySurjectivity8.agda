{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity8 where

postulate 𝔛 : Set
postulate 𝔒 : 𝔛 → Set

postulate ax bx : 𝔛

Arrow : Set
Arrow = 𝔒 ax → 𝔒 bx

Extended : (H : 𝔒 bx → Set) → Arrow → Set
Extended H f = ∀ (l : 𝔒 ax) → H (f l)

postulate Property : (b : 𝔛) (R : ∀ (y : 𝔛) → Arrow → Set) → Set₁
postulate Upper : ∀ (𝔓 : 𝔛 → Set₁) → Set₁

record 𝓢urjectivity (T : Set₁) : Set₁ where
  field
    surjectivity : Arrow → T

open 𝓢urjectivity ⦃ … ⦄ public

instance
  postulate
    ExtendedPropertySurjectivity : {R : 𝔒 bx → Set} → 𝓢urjectivity (Upper (λ v → Property v (λ w → Extended R)))

module _
  (R : 𝔒 bx → Set)
  where

  works : Arrow → Upper (λ v → Property v (λ w → Extended R))
  works = surjectivity ⦃ ExtendedPropertySurjectivity {R = R} ⦄

  fails : Arrow → Upper (λ v → Property v (λ w → Extended R))
  fails = surjectivity
