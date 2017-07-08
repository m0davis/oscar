--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  postulate ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  --ṖropertyEquivalence P Q = ∀ {n f} → (P n f → Q _ f) × (Q _ f → P _ f)
  --ṖropertyEquivalence P Q = ∀ {n f} → (P {n} f → Q f) × (Q f → P f)

  instance

    postulate IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence

instance
 postulate
  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
--  HasEquivalenceṖroperty .HasEquivalence.Equivalence = ṖropertyEquivalence

record Lift {a ℓ} (A : Set a) : Set (a ∙̂ ℓ) where
  constructor lift
  field lower : A

open Lift public

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
  ProperthingṖroperty .Properthing.➊ _ = Lift 𝟙
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
