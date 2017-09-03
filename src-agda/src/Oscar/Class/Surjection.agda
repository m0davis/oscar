
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.Surjection where

module Surjection
  {𝔬₁} (𝔒₁ : Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : Ø 𝔬₂)
  = ℭLASS (𝔒₁ , 𝔒₂) (𝔒₁ → 𝔒₂)

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  where
  surjection = Surjection.method 𝔒₁ 𝔒₂
  instance
    toUnit : ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄ → Unit.class (Surjection.type 𝔒₁ 𝔒₂)
    toUnit .⋆ = surjection
