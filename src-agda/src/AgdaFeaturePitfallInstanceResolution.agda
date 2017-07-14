
module AgdaFeaturePitfallInstanceResolution where

infixr 5 _,_
record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
  constructor _,_
  field
    π₀ : 𝔒
    π₁ : 𝔓 π₀

open Σ public

Property : Set → Set₁
Property P = P → Set

ExtensionProperty : ∀ (𝔒 : Set)
  → Set₁
ExtensionProperty 𝔒 = Σ (𝔒 → Set) (λ P → ∀ f → P f)

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
    PropertyEquivalence : Property 𝔒 → Property 𝔒 → Set

module _
  {𝔒 : Set}
  where

  _≈_ : ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  postulate
    instance
      𝓢ymmetryExtensionProperty : 𝓢ymmetry _≈_

  test-sym-ext2 : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-sym-ext2 {P} {Q} P≈Q = 𝓢ymmetryExtensionProperty .𝓢ymmetry.symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  test-sym-ext3 : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-sym-ext3 {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

  test-sym-ext-fails1 : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-sym-ext-fails1 {P} {Q} P≈Q = 𝓢ymmetryExtensionProperty .𝓢ymmetry.symmetry {x = _ , _} {y = _ , _} P≈Q

  test-sym-ext-fails2 : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-sym-ext-fails2 P≈Q = symmetry P≈Q
