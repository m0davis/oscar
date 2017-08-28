
open import Oscar.Prelude
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Proposequality
import Oscar.Class.Surjection.⋆

module Oscar.Data.Surjcollation where

𝓼urjcollation : ∀ {𝔵 𝔞 𝔟} {𝔛 : Ø 𝔵}
  𝔟̇
  (𝔅 : 𝔛 → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛)
  → Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔟̇
𝓼urjcollation 𝔟̇ 𝔅 𝔄 = ∀ {m} → 𝔅 m → 𝔅 m → LeftṖroperty 𝔟̇ 𝔄 m

module _ {𝔵 𝔞 𝔟 𝔟̇} {𝔛 : Ø 𝔵}
  (𝔅 : 𝔛 → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛)
  ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
  (𝔅̇ : ∀̇ π̂² 𝔟̇ 𝔅)
  (let infix 4 _⟨𝔅̇⟩_
       _⟨𝔅̇⟩_ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇
       _⟨𝔅̇⟩_ p q = 𝔅̇ p q)
  where
  surjcollation[_]⟦_/_⟧ : 𝓼urjcollation 𝔟̇ 𝔅 𝔄
  surjcollation[_]⟦_/_⟧ p q .π₀ x = x ◃ p ⟨𝔅̇⟩ x ◃ q

module _ {𝔵 𝔞 𝔟 𝔟̇} {𝔛 : Ø 𝔵} {𝔅 : 𝔛 → Ø 𝔟}
  (𝔄 : π̂² 𝔞 𝔛)
  ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
  (𝔅̇ : ∀̇ π̂² 𝔟̇ 𝔅)
  where
  surjcollation⟦_/_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ ⟧

module _ {𝔵 𝔞} {𝔛 : Ø 𝔵}
  (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
    {𝔟̇} {𝔅̇ : ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇}
  where
  surjcollation⟦_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ ⟧

module _ {𝔵 𝔞 𝔟} {𝔛 : Ø 𝔵}
  (𝔅 : 𝔛 → Ø 𝔟)
  (𝔄 : π̂² 𝔞 𝔛)
    ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
  where
  ≡-surjcollation[_]⟦_⟧ = surjcollation[ 𝔅 ]⟦ 𝔄 / _≡_ ⟧

module _ {𝔵 𝔞} {𝔛 : Ø 𝔵}
  (𝔄 : π̂² 𝔞 𝔛)
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟} ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
  where
  ≡-surjcollation⟦_⟧ = ≡-surjcollation[ 𝔅 ]⟦ 𝔄 ⟧

module _ {𝔵 𝔞} {𝔛 : Ø 𝔵} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
  where
  ≡-surjcollation = ≡-surjcollation⟦ 𝔄 ⟧

module Surjcollation {𝔵 𝔞 𝔟̇} {𝔛 : Ø 𝔵}
  (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  (𝔅̇ : ∀ {𝔟} {𝔅 : 𝔛 → Ø 𝔟} → (∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇))
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    ⦃ _ : Surjectextensivity.class 𝔄 𝔅 ⦄
  where
  method = surjcollation[ 𝔅 ]⟦ 𝔄 / 𝔅̇ {𝔅 = 𝔅} ⟧

  infix 18 _⟹_
  _⟹_ = method
