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

  ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ṖropertyEquivalence P Q = ∀ {n f} → (P n f → Q _ f) × (Q _ f → P _ f)

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence
    𝓢ymmetryṖroperty .𝓢ymmetry.symmetry P⇔Q = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity P⇔Q Q⇔R = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence
    IsEquivalenceṖroperty = ∁

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .HasEquivalence.Equivalence P Q = ṖropertyEquivalence P Q

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
  ProperthingṖroperty .Properthing.➊ _ _ = Lift 𝟙
  ProperthingṖroperty .Properthing._∧_ P Q _ f = P _ f × Q _ f
  ProperthingṖroperty .Properthing.⌶HasEquivalence = !
  ProperthingṖroperty {𝔒 = 𝔒} .Properthing.Nothing P = ∀ {n} {f : 𝔒 n} → P _ f → 𝟘
  ProperthingṖroperty .Properthing.fact2 P⇔Q NoP Q = NoP $ π₁ P⇔Q Q

module Test where
  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  open Substitunction 𝔓

  instance

    [Propertyish]Substitunction : ∀ {m} → [Propertyish] (Substitunction m)
    [Propertyish]Substitunction = ∁

  postulate
    foo : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → ➊ ≈ P

  left-identity-∧ : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → (➊ ∧ P) ≈ P
  left-identity-∧ P .π₀ (π₂ , π₃) = π₃
  left-identity-∧ P .π₁ x .π₀ = lift ∅
  left-identity-∧ P .π₁ x .π₁ = x
