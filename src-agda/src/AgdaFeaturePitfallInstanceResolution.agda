
module AgdaFeaturePitfallInstanceResolution where

infixr 5 _,_
record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
  constructor _,_
  field
    π₀ : 𝔒
    π₁ : 𝔓 π₀

open Σ public

Ṗroperty : Set → Set₁
Ṗroperty P = P → Set

ExtensionṖroperty : ∀ (𝔒 : Set) (_↦_ : 𝔒 → 𝔒 → Set)
  → Set₁
ExtensionṖroperty 𝔒 _↦_ = Σ (𝔒 → Set) (λ P → ∀ (f g : 𝔒) → f ↦ g → P f → P g)

module _
  {𝔒 : Set₁}
  (_∼_ : 𝔒 → 𝔒 → Set)
  where
  𝓼ymmetry = ∀ {x y} → x ∼ y → y ∼ x
  record 𝓢ymmetry : Set₁ where field symmetry : 𝓼ymmetry

open 𝓢ymmetry ⦃ … ⦄ public

module _
  {𝔒 : Set}
  where

  postulate
    ṖropertyEquivalence : Ṗroperty 𝔒 → Ṗroperty 𝔒 → Set

module _
  {𝔒 : Set}
  {_↦_ : 𝔒 → 𝔒 → Set}
  where

  _≈_ : ExtensionṖroperty 𝔒 _↦_ → ExtensionṖroperty 𝔒 _↦_ → Set
  _≈_ P Q = ṖropertyEquivalence (π₀ P) (π₀ Q)

  postulate
    instance
      𝓢ymmetryExtensionṖroperty : 𝓢ymmetry _≈_

  test-sym-ext2 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext2 {P} {Q} P≈Q = 𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  test-sym-ext3 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext3 {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

  test-sym-ext-fails1 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext-fails1 {P} {Q} P≈Q = 𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry {x = _ , _} {y = _ , _} P≈Q

  test-sym-ext-fails2 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext-fails2 P≈Q = symmetry P≈Q
