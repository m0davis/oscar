
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Leftunit
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity

module Oscar.Class.Transrightidentity where

module Transrightidentity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  (ε : Reflexivity.type _∼_)
  (transitivity : Transitivity.type _∼_)
  = ℭLASS (_∼_ ,, (λ {x y} → _∼̇_ {x} {y}) ,, (λ {x} → ε {x}) ,, (λ {x y z} → transitivity {x} {y} {z}))
          (∀ {x y} {f : x ∼ y} → Leftunit.type _∼̇_ ε transitivity f)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  {ε : Reflexivity.type _∼_}
  {transitivity : Transitivity.type _∼_}
  where
  transrightidentity = Transrightidentity.method _∼_ _∼̇_ ε transitivity
  instance
    toLeftunitFromTransrightidentity :
      ⦃ _ : Transrightidentity.class _∼_ _∼̇_ ε transitivity ⦄
      → ∀ {x y} {f : x ∼ y} → Leftunit.class _∼̇_ ε transitivity f
    toLeftunitFromTransrightidentity .⋆ = transrightidentity

module Transrightidentity!
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : Reflexivity.class _∼_ ⦄
  ⦃ _ : Transitivity.class _∼_ ⦄
  = Transrightidentity (_∼_) (_∼̇_) reflexivity transitivity
