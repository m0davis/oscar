
module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Property

module TestEquivalenceExtensionṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  test-sym-ext1 : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext1 P≈Q = 𝓢ymmetryṖroperty .𝓢ymmetry.symmetry P≈Q

  test-sym-ext2 : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext2 {P} {Q} P≈Q = 𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  test-sym-ext3 : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext3 {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

  test-sym-ext-fails : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext-fails P≈Q = symmetry P≈Q
