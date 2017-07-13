
module AgdaFeaturePitfallInstanceResolution where

infixr 5 _,_
record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
  constructor _,_
  field
    π₀ : 𝔒
    π₁ : 𝔓 π₀

open Σ public

record V {𝔵} (𝔛 : Set 𝔵) : Set 𝔵 where
  constructor ∁
  field
    π₀ : 𝔛

open V public

Ṗroperty : ∀ {𝔛 : Set} → (𝔛 → Set) → Set₁
Ṗroperty P = V (∀ {x} → P x → Set)

ExtensionṖroperty : ∀ {𝔛 : Set}
  (𝔒 : 𝔛 → Set) (_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Set)
  → Set₁
ExtensionṖroperty 𝔒 _↦_ = Σ (V (∀ {x} → 𝔒 x → Set)) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → π₀ P f → π₀ P g)

module _
  {𝔒 : Set₁}
  (_∼_ : 𝔒 → 𝔒 → Set)
  where
  𝓼ymmetry = ∀ {x y} → x ∼ y → y ∼ x
  record 𝓢ymmetry : Set₁ where field symmetry : 𝓼ymmetry

open 𝓢ymmetry ⦃ … ⦄ public

module _
  {𝔛 : Set}
  {𝔒 : 𝔛 → Set}
  where

  postulate
    ṖropertyEquivalence : Ṗroperty 𝔒 → Ṗroperty 𝔒 → Set
    instance 𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence

module _
  {𝔛 : Set}
  {𝔒 : 𝔛 → Set}
  {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Set}
  where

  _≈_ : ExtensionṖroperty 𝔒 _↦_ → ExtensionṖroperty 𝔒 _↦_ → Set
  _≈_ P Q = ṖropertyEquivalence (π₀ P) (π₀ Q)

  postulate
    instance
      𝓢ymmetryExtensionṖroperty : 𝓢ymmetry _≈_

  test-sym-ext1 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext1 P≈Q = 𝓢ymmetryṖroperty .𝓢ymmetry.symmetry P≈Q

  test-sym-ext2 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext2 {P} {Q} P≈Q = 𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  test-sym-ext3 : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext3 {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

  test-sym-ext-fails : {P Q : ExtensionṖroperty 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext-fails P≈Q = symmetry P≈Q
