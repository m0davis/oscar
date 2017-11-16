{-# OPTIONS --instance-search-depth=5 --show-implicit #-}

open import Oscar.Prelude
open import Oscar.Class.Smap
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Surjcollation
import Oscar.Class.Surjection.⋆

module Oscar.Data.Surjextenscollation where

module _ {𝔵 𝔞 𝔞̇ 𝔟 𝔟̇} {𝔛 : Ø 𝔵}
  (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  (𝔅 : 𝔛 → Ø 𝔟)
  ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
  (let ℭ : 𝔛 → Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔞̇ ∙̂ ↑̂ 𝔟̇
       ℭ = LeftExtensionṖroperty 𝔟̇ 𝔄 𝔄̇)
  (𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇)
    ⦃ _ : ∀ {y} → Symmetry.class (𝔅̇ {y}) ⦄
    ⦃ _ : ∀ {y} → Transitivity.class (𝔅̇ {y}) ⦄
    ⦃ _ : Surjextensionality!.class 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where

  surjextenscollation[_/_]⟦_/_⟧ : ∀ {m} → 𝔅 m → 𝔅 m → ℭ m
  surjextenscollation[_/_]⟦_/_⟧ s t =
    surjcollation⟦ 𝔄 / 𝔅̇ ⟧ s t , λ f≐g f◃s=f◃t →
      -- FIXME this (`surjextensionality[ Pointwise 𝔅̇ ] ⦃ ! ⦄ f≐g t ∙ f◃s=f◃t ∙ symmetry (surjextensionality[ Pointwise 𝔅̇ ] ⦃ ! ⦄ f≐g s)`) used to be a workaround for "instance search depth exhausted", but now does not seem to help. See the FIXME note in Oscar.Class.Surjextensionality.
      ⟪ f≐g ⟫[ Pointwise 𝔅̇ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise 𝔅̇ ] s)

module _ {𝔵 𝔞 𝔞̇} {𝔛 : Ø 𝔵} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
  (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    {𝔟̇} {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇}
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
    ⦃ _ : ∀ {y} → Symmetry.class (𝔅̇ {y}) ⦄
    ⦃ _ : ∀ {y} → Transitivity.class (𝔅̇ {y}) ⦄
    ⦃ _ : Surjextensionality!.class 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where
  surjextenscollation⟦_⟧ = surjextenscollation[ 𝔄 / 𝔅 ]⟦ 𝔄̇ / 𝔅̇ ⟧

module _ {𝔵 𝔞 𝔞̇ 𝔟 𝔟̇} {𝔛 : Ø 𝔵} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞} {𝔅 : 𝔛 → Ø 𝔟}
  (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
  (𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇)
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
    ⦃ _ : ∀ {y} → Symmetry.class (𝔅̇ {y}) ⦄
    ⦃ _ : ∀ {y} → Transitivity.class (𝔅̇ {y}) ⦄
    ⦃ _ : Surjextensionality!.class 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where
  surjextenscollation⟦_/_⟧ = surjextenscollation[ 𝔄 / 𝔅 ]⟦ 𝔄̇ / 𝔅̇ ⟧

module Surjextenscollation
  {𝔵 𝔞 𝔞̇} {𝔛 : Ø 𝔵}
  (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  (𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞̇)
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    {𝔟̇} {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇}
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
    ⦃ _ : ∀ {y} → Symmetry.class (𝔅̇ {y}) ⦄
    ⦃ _ : ∀ {y} → Transitivity.class (𝔅̇ {y}) ⦄
    ⦃ _ : Surjextensionality!.class 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where
  method = surjextenscollation[ 𝔄 / 𝔅 ]⟦ 𝔄̇ / 𝔅̇ ⟧

  infix 18 _⟹_
  _⟹_ = method

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂} {𝔄₂ : 𝔛 → Ø 𝔞₂}
 (𝔄 : 𝔛 → 𝔛 → Ø 𝔞₁ ∙̂ 𝔞₂)
  ⦃ _ : 𝔄 ≡ Arrow 𝔄₁ 𝔄₂ ⦄
  (let 𝔄 = Arrow 𝔄₁ 𝔄₂)
  where
  open Surjextenscollation 𝔄 _≡̇_ public using () renaming (method to ≡-surjextenscollation⟦_⟧) public
