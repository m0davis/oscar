
open import Oscar.Prelude
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
import Oscar.Class.Surjectextensivity.SurjectivityExtension
open import Oscar.Data.Proposequality
import Oscar.Class.Surjection.⋆

module Oscar.Data.Surjcollation where

Constant' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔟} {𝔟̇} {_ : 𝔛 → Ø 𝔟} → ∀ 𝔟̇′ {𝔟′} → (𝔛 → Ø 𝔟′) → Ø 𝔵 ∙̂ 𝔟′ ∙̂ ↑̂ 𝔟̇′
Constant' {𝔟 = 𝔟} {𝔟̇} {𝔅} 𝔟̇′ {𝔟′} 𝔅′ = Lift (Σ ((𝔟̇′ ≡ 𝔟̇) × (𝔟′ ≡ 𝔟)) λ {(∅ , ∅) → 𝔅′ ≡ 𝔅})

getConstant' : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇}
  → ∀ {𝔟̇′ 𝔟′} {𝔅′ : 𝔛 → Ø 𝔟′}
    ⦃ _ : Constant' {𝔟̇ = 𝔟̇} {𝔅} 𝔟̇′ 𝔅′ ⦄
  → (𝔅̇ : Wrap (∀̇ π̂² 𝔟̇ 𝔅)) → Wrap (∀ {x} → 𝔅′ x → 𝔅′ x → Ø 𝔟̇′)
getConstant' {{lift ((∅ , ∅) , ∅) }} = ¡

record Constant {𝔵} {𝔛 : Ø 𝔵} {𝔟} {𝔟̇ : Ł} {𝔅 : 𝔛 → Ø 𝔟} 𝔟̇′ {𝔟′} (𝔅′ : 𝔛 → Ø 𝔟′) : Ø 𝔵 ∙̂ 𝔟′ ∙̂ ↑̂ 𝔟̇′ where
  instance constructor lift
  field lower : Σ ((𝔟̇′ ≡ 𝔟̇) × (𝔟′ ≡ 𝔟)) λ {(∅ , ∅) → 𝔅′ ≡ 𝔅}

open Constant ⦃ … ⦄

getConstant : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇}
  → ∀ {𝔟̇′ 𝔟′} {𝔅′ : 𝔛 → Ø 𝔟′}
    ⦃ _ : Constant {𝔟̇ = 𝔟̇} {𝔅} 𝔟̇′ 𝔅′ ⦄
  → (𝔅̇ : Wrap (∀̇ π̂² 𝔟̇ 𝔅)) → Wrap (∀̇ π̂² 𝔟̇′ 𝔅′)
getConstant ⦃ lift ((∅ , ∅) , ∅) ⦄ = ¡

𝓼urjcollation : ∀
  {𝔵} {𝔛 : Ø 𝔵} {𝔟} {𝔞}
 𝔟̇
 (𝔄 : π̂² 𝔞 𝔛)
 (𝔅 : 𝔛 → Ø 𝔟)
  → Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔟̇
𝓼urjcollation 𝔟̇ 𝔄 𝔅 = ∀ {m} → 𝔅 m → 𝔅 m → LeftṖroperty 𝔟̇ 𝔄 m

module Surjcollation
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
 (ℬ̇ : ∀ 𝔟̇ {𝔟} → (𝔛 → Ø 𝔟) → Ø 𝔵 ∙̂ 𝔟 ∙̂ ↑̂ 𝔟̇)
 (𝔅̇ : ∀ {𝔟̇ 𝔟} {𝔅 : 𝔛 → Ø 𝔟} ⦃ _ : ℬ̇ 𝔟̇ 𝔅 ⦄ → Wrap (∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇))
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇}
  ⦃ _ : ℬ̇ 𝔟̇ 𝔅 ⦄
  (let infix 4 _⟨𝔅̇⟩_
       _⟨𝔅̇⟩_ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇
       _⟨𝔅̇⟩_ {x} p q = π₀ 𝔅̇ {x} p q)
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  where

  surjcollation : 𝓼urjcollation 𝔟̇ 𝔄 𝔅
  surjcollation p q .π₀ x = x ◃ p ⟨𝔅̇⟩ x ◃ q

  infix 18 _⟹_
  _⟹_ = surjcollation

module SurjcollationOperator
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔟̇}
 (𝔅̇ : ∀ {𝔟} {𝔅 : 𝔛 → Ø 𝔟} → (∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇))
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  where
  open Surjcollation 𝔄 (λ 𝔟̇₁ x → Lift (𝔟̇₁ ≡ 𝔟̇)) (λ { {𝔅 = 𝔅'} ⦃ lift ∅ ⦄ → ∁ (λ {y} → 𝔅̇ {𝔅 = 𝔅'} {x = y})}) ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ public

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : π̂² 𝔞 𝔛)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  {𝔟̇}
 (𝔅̇ : Wrap (∀̇ π̂² 𝔟̇ 𝔅))
  where
  open Surjcollation 𝔄 Constant (getConstant 𝔅̇) ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ public using () renaming (surjcollation to surjcollation⟦_/_⟧)

module Surjcollation'
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  {𝔟̇} {𝔅̇ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇}
  where
  open Surjcollation 𝔄 Constant (getConstant (∁ (λ {x} → 𝔅̇ {x}))) public

open Surjcollation' public using () renaming (surjcollation to surjcollation⟦_⟧)

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : π̂² 𝔞 𝔛)
  {𝔟}
 (𝔅 : 𝔛 → Ø 𝔟)
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  where
  open Surjcollation' 𝔄 {𝔅 = 𝔅} {𝔅̇ = Proposequality} public using () renaming (surjcollation to ≡-surjcollation⟦_/_⟧)

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
 (𝔄 : π̂² 𝔞 𝔛)
  where
  open SurjcollationOperator 𝔄 _≡_ public using () renaming (surjcollation to ≡-surjcollation⟦_⟧)

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞}
  {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
  where
  open SurjcollationOperator 𝔄 _≡_ public using () renaming (surjcollation to ≡-surjcollation)

module Surjextenscollation
  {𝔵} {𝔛 : Ø 𝔵} {𝔞₁}
  {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂}
  {𝔄₂ : 𝔛 → Ø 𝔞₂}
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  {𝔞̇₂}
 (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇₂)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇}
  (let ℭ : 𝔛 → Ø 𝔵 ∙̂ 𝔞₁ ∙̂ 𝔞₂ ∙̂ 𝔞̇₂ ∙̂ ↑̂ 𝔟̇
       ℭ = LeftExtensionṖroperty 𝔟̇ 𝔄 𝔄̇)
 (𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇)
  ⦃ _ : ∀ {y} → 𝓢ymmetry (𝔅̇ {y}) ⦄
  ⦃ _ : ∀ {y} → 𝓣ransitivity (𝔅̇ {y}) ⦄
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : [𝓢urjextensionality] 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  ⦃ _ : 𝓢urjextensionality 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where

  surjextenscollation : ∀ {m} → 𝔅 m → 𝔅 m → ℭ m
  surjextenscollation s t =
    surjcollation⟦ 𝔄 / ∁ 𝔅̇ ⟧ s t , λ f≐g f◃s=f◃t →
      ⟪ f≐g ⟫[ Pointwise 𝔅̇ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise 𝔅̇ ] s)

  infix 18 _⟹_
  _⟹_ = surjextenscollation

module Surjextenscollation'
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} (𝔄₁ : 𝔛 → Ø 𝔞₁)
  {𝔞₂} (𝔄₂ : 𝔛 → Ø 𝔞₂)
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  {𝔞̇}
    (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇} {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇}
  where
  open Surjextenscollation (λ {x} {y} → 𝔄̇ {x} {y}) (λ {y} → 𝔅̇ {y}) public

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂} {𝔄₂ : 𝔛 → Ø 𝔞₂}
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  {𝔞̇}
 (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇} {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇}
  where
  open Surjextenscollation (λ {x} {y} → 𝔄̇ {x} {y}) (λ {y} → 𝔅̇ {y}) public using () renaming (surjextenscollation to surjextenscollation⟦_⟧)

module SurjextenscollationOperator
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂} {𝔄₂ : 𝔛 → Ø 𝔞₂}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞₁ ∙̂ 𝔞₂)
  ⦃ _ : 𝔄 ≡ Arrow 𝔄₁ 𝔄₂ ⦄
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  {𝔞̇}
 (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇} {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇}
  where
  open Surjextenscollation (λ {x} {y} → 𝔄̇ {x} {y}) (λ {y} → 𝔅̇ {y}) public

open SurjextenscollationOperator using () renaming (surjextenscollation to surjextenscollation⟦_/_⟧) public

module ≡-SurjextenscollationOperator
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂} {𝔄₂ : 𝔛 → Ø 𝔞₂}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞₁ ∙̂ 𝔞₂)
  ⦃ _ : 𝔄 ≡ Arrow 𝔄₁ 𝔄₂ ⦄
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  where
  open SurjextenscollationOperator 𝔄 _≡̇_ public

open ≡-SurjextenscollationOperator using () renaming (surjextenscollation to ≡-surjextenscollation[_]) public
