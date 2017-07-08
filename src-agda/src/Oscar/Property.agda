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

record [Propertyish] {𝔵} {𝔛 : Ø 𝔵} {𝔬} (𝔒 : 𝔛 → Ø 𝔬) : Ø₀ where
  no-eta-equality
  constructor ∁

instance

  ProperthingṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    ⦃ _ : [Propertyish] 𝔒 ⦄
    {ℓ}
    → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (Ṗroperty ℓ 𝔒)
  --ProperthingṖroperty .Properthing.➊ _ _ = Lift 𝟙
  ProperthingṖroperty .Properthing.➊ _ = magic
  ProperthingṖroperty .Properthing._∧_ P Q = magic

module Test where
  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  open Substitunction 𝔓

  instance

    [Propertyish]Substitunction : ∀ {m} → [Propertyish] (Substitunction m)
    [Propertyish]Substitunction = ∁

  postulate
    works : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → ((λ {x} → ((λ {x} → ➊ ⦃ ProperthingṖroperty ⦄ {x = x}) ∧ (λ {x} → P {x})) {x}) ≈ (λ {x} → P {x}))
    fails : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → ((λ {x} → ((λ {x} → ➊ ⦃ ! ⦄ {x = x}) ∧ (λ {x} → P {x})) {x}) ≈ (λ {x} → P {x}))
    --worksfoo : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → (➊ ∧ P) ≈ P
