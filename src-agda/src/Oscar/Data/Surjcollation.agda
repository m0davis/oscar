
open import Oscar.Prelude
open import Oscar.Class.Smap
open import Oscar.Data.Proposequality
open import Oscar.Class.Surjection

module Oscar.Data.Surjcollation where

𝓼urjcollation : ∀ {𝔵₁ 𝔵₂ 𝔞 𝔟} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  𝔟̇
  (𝔅 : 𝔛₂ → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛₁)
  → Ø 𝔵₁ ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔟̇
𝓼urjcollation surjection 𝔟̇ 𝔅 𝔄 = ∀ {m} → 𝔅 (surjection m) → 𝔅 (surjection m) → LeftṖroperty 𝔟̇ 𝔄 m

module _ {𝔵₁ 𝔵₂ 𝔞 𝔟 𝔟̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔅 : 𝔛₂ → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛₁)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  (𝔅̇ : ∀̇ π̂² 𝔟̇ 𝔅)
  (let infix 4 _⟨𝔅̇⟩_
       _⟨𝔅̇⟩_ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇
       _⟨𝔅̇⟩_ p q = 𝔅̇ p q)
  where
  surjcollation[_]⟦_/_⟧ : 𝓼urjcollation surjection 𝔟̇ 𝔅 𝔄
  surjcollation[_]⟦_/_⟧ p q .π₀ x = x ◃ p ⟨𝔅̇⟩ x ◃ q

module _ {𝔵₁ 𝔵₂ 𝔞 𝔟 𝔟̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂} {𝔅 : 𝔛₂ → Ø 𝔟}
  (𝔄 : π̂² 𝔞 𝔛₁)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  (𝔅̇ : ∀̇ π̂² 𝔟̇ 𝔅)
  where
  surjcollation⟦_/_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ ⟧

module _ {𝔵₁ 𝔵₂ 𝔞} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔄 : 𝔛₁ → 𝔛₁ → Ø 𝔞)
    {𝔟} {𝔅 : 𝔛₂ → Ø 𝔟}
    ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
    {𝔟̇} {𝔅̇ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇}
  where
  surjcollation⟦_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ ⟧

module _ {𝔵₁ 𝔵₂ 𝔞 𝔟} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (𝔅 : 𝔛₂ → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛₁)
    ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  where
  ≡-surjcollation[_]⟦_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / _≡_ ⟧

module _ {𝔵₁ 𝔞} {𝔛₁ : Ø 𝔵₁}
  (𝔄 : π̂² 𝔞 𝔛₁)
    {𝔵₂} {𝔛₂ : Ø 𝔵₂} ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
    {𝔟} {𝔅 : 𝔛₂ → Ø 𝔟} ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  where
  ≡-surjcollation⟦_⟧ = ≡-surjcollation[ 𝔅 ]⟦ 𝔄 ⟧

module _ {𝔵₁ 𝔞} {𝔛₁ : Ø 𝔵₁} {𝔄 : π̂² 𝔞 𝔛₁}
  where
  ≡-surjcollation = ≡-surjcollation⟦ 𝔄 ⟧

module Surjcollation {𝔵₁ 𝔵₂ 𝔞 𝔟̇} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂} ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  (𝔄 : 𝔛₁ → 𝔛₁ → Ø 𝔞)
  (𝔅̇ : ∀ {𝔟} {𝔅 : 𝔛₂ → Ø 𝔟} → (∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇))
    {𝔟} {𝔅 : 𝔛₂ → Ø 𝔟}
    ⦃ _ : Smaphomarrow!.class 𝔄 𝔅 ⦄
  where
  method = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ {𝔅 = 𝔅} ⟧

  infix 18 _⟹_
  _⟹_ = method
