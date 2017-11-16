
open import Everything

module Test.EquivalenceExtensionṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  test-sym-ext : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext P≈Q = symmetry P≈Q

  test-trans-ext : {P Q R : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-ext P≈Q Q≈R = transitivity P≈Q Q≈R
