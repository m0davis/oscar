{-# OPTIONS --show-implicit #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  postulate
    instance HasEquivalenceṖroperty : HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    instance HasEquivalenceṖroperty' : HasEquivalence (Ṗroperty' ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    instance HasEquivalenceṖropertyW : HasEquivalence (ṖropertyWrapper ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)

record [Propertyish] {𝔵} {𝔛 : Ø 𝔵} {𝔬} (𝔒 : 𝔛 → Ø 𝔬) : Ø₀ where
  no-eta-equality
  constructor ∁

instance
  postulate ProperthingṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬} {𝔒 : 𝔛 → Ø 𝔬} ⦃ _ : [Propertyish] 𝔒 ⦄ {ℓ} → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (Ṗroperty ℓ 𝔒)
  postulate ProperthingṖroperty' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬} {𝔒 : 𝔛 → Ø 𝔬} ⦃ _ : [Propertyish] 𝔒 ⦄ {ℓ} → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (Ṗroperty' ℓ 𝔒)
  postulate ProperthingṖropertyW : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬} {𝔒 : 𝔛 → Ø 𝔬} ⦃ _ : [Propertyish] 𝔒 ⦄ {ℓ} → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (ṖropertyWrapper ℓ 𝔒)

module Test where
  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  open Substitunction 𝔓

  instance

    [Propertyish]Substitunction : ∀ {m} → [Propertyish] (Substitunction m)
    [Propertyish]Substitunction = ∁

  postulate
    works1 : ∀ {m} (P : Ṗroperty ℓ (Substitunction m)) → ((λ {x} → ((λ {x} → ➊ {𝔒 = Ṗroperty ℓ (Substitunction m)} ⦃ ProperthingṖroperty ⦄ {x = x})) {x}) ≈ (λ {x} → P {x}))
    works2 : ∀ {m} (P : Ṗroperty ℓ (Substitunction m)) → ((λ {x} → ((λ {x} → ➊ {𝔒 = Ṗroperty _ _} {x = x})) {x}) ≈ (λ {x} → P {x}))
    works3 : ∀ {m} (P : Ṗroperty ℓ (Substitunction m)) → ((λ {x} → ➊ {𝔒 = Ṗroperty _ _} {x}) ≈ P)
    works4 : ∀ {m} (P : Ṗroperty ℓ (Substitunction m)) → ((λ {x} → ((λ {x} → ➊ {𝔒 = Ṗroperty _ _} {x = x})) {x}) ≈[ ({x : ¶} → π̂ {∅̂} ℓ (Substitunction m x)) ] (λ {x} → P {x}))
    works' : ∀ {m} (P : Ṗroperty' ℓ (Substitunction m)) → ➊ ≈ P
    worksW : ∀ {m} (P : ṖropertyWrapper ℓ (Substitunction m)) → ➊ ≈ P
    fails : ∀ {m} (P : Ṗroperty ℓ (Substitunction m)) → (λ {x} → ➊ ⦃ ! ⦄ {x = x}) ≈ (λ {x} → P {x})
