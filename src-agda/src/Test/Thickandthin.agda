
open import Everything

module Test.Thickandthin where

module _ {x a b ℓb c ℓc} ⦃ _ : Thickandthin x a b ℓb c ℓc ⦄ where
  open Thickandthin ⦃ … ⦄

  test-thin : 𝓽hin A B
  test-thin = thin

  test-check/thin=1 : 𝓬heck/thin=1 A B C _≈C_
  test-check/thin=1 = check/thin=1

  test-injectivity : ∀ {m : X} {x : A (⇑₀ m)} → 𝓶ap (_≈B_ on thin x) _≈B_
  test-injectivity {x = x} = injectivity₂,₁ x
