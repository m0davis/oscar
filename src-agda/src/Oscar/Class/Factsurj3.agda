
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Proposequality

module Oscar.Class.Factsurj3 where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̈ 𝔞̇ ℓ̇}
  (𝔄̈ : π̂² 𝔞̈ 𝔄)
  (𝔄̇ : π̂ 𝔞̇ 𝔄)
  ⦃ _ : 𝓡eflexivity 𝔄̈ ⦄
  ⦃ _ : 𝓢urjectextensivity 𝔄̈ 𝔄̇ ⦄
  ⦃ _ : ∀ {x} → HasEquivalence (𝔄̇ x) ℓ̇ ⦄
  {a} (ȧ : 𝔄̇ a)
  where
  [𝓯actsurj3] = ȧ ≈ ε[ 𝔄̈ ] ◃ ȧ

module _
  {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : 𝔄 → Ø 𝔟}
  (type : ∀ {a} (B : 𝔅 a) → Ø ℓ)
  where
  𝒻actsurj3 = ∀ {a} {b : 𝔅 a} → type b
  record [𝐹actsurj3] 𝔯 : Ø 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔯 ∙̂ ↑̂ ℓ where
    constructor ∁
    field
      _∼ᵣ_ : π̂² 𝔯 𝔄
      ⦃ ⌶Reflexivity ⦄ : 𝓡eflexivity _∼ᵣ_
      ⦃ ⌶Surjectextensivity ⦄ : 𝓢urjectextensivity _∼ᵣ_ 𝔅
      ⦃ ⌶HasEquivalence ⦄ : ∀ {x} → HasEquivalence (𝔅 x) ℓ
      ⦃ ⌶CorrectFactsurj3 ⦄ : (λ {a} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {a}) ≡ type

  record 𝐹actsurj3 {𝔯} ⦃ _ : [𝐹actsurj3] 𝔯 ⦄ : Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ where
    field factsurj3 : 𝒻actsurj3

open 𝐹actsurj3 ⦃ … ⦄ public

module _
  {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔄)
  ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄
  ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔅 ⦄
  ⦃ _ : ∀ {x} → HasEquivalence (𝔅 x) ℓ ⦄
  where
  𝓯actsurj3 = 𝒻actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
  [𝓕actsurj3] = [𝐹actsurj3] (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
  𝓕actsurj3 = 𝐹actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
