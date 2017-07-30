
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Proposequality

module Oscar.Class.Factsurj3 where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̈ 𝔞̇ 𝔞̇̈}
  (𝔄̈ : π̂² 𝔞̈ 𝔄)
  (𝔄̇ : π̂ 𝔞̇ 𝔄)
  ⦃ _ : 𝓡eflexivity 𝔄̈ ⦄
  ⦃ _ : 𝓢urjectextensivity 𝔄̈ 𝔄̇ ⦄
  ⦃ _ : ∀ {𝒶} → HasEquivalence (𝔄̇ 𝒶) 𝔞̇̈ ⦄
  where
  [𝒻actsurj3] : Ṗroperty 𝔞̇̈ 𝔄̇
  [𝒻actsurj3] .π₀ 𝒶̇ = 𝒶̇ ≈ ε[ 𝔄̈ ] ◃ 𝒶̇

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̇} {𝔄̇ : 𝔄 → Ø 𝔞̇} {𝔞̇̈}
  (𝔄̇̇ : Ṗroperty 𝔞̇̈ 𝔄̇)
  where
  𝒻actsurj3 = ∀ {𝒶} {𝒶̇ : 𝔄̇ 𝒶} → π₀ 𝔄̇̇ 𝒶̇
  module _
    𝔞̈
    where
    record [ℱactsurj3] : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ ↑̂ 𝔞̈ ∙̂ ↑̂ 𝔞̇̈ where
      constructor ∁
      field
        𝔄̈ : π̂² 𝔞̈ 𝔄
        ⦃ ⌶Reflexivity ⦄ : 𝓡eflexivity 𝔄̈
        ⦃ ⌶Surjectextensivity ⦄ : 𝓢urjectextensivity 𝔄̈ 𝔄̇
        ⦃ ⌶HasEquivalence ⦄ : ∀ {𝒶} → HasEquivalence (𝔄̇ 𝒶) 𝔞̇̈
        ⦃ ⌶CorrectFactsurj3 ⦄ : [𝒻actsurj3] 𝔄̈ 𝔄̇ ≡ 𝔄̇̇
  module _
    {𝔞̈}
    ⦃ _ : [ℱactsurj3] 𝔞̈ ⦄
    where
    record ℱactsurj3 : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ 𝔞̇̈ where
      field factsurj3 : 𝒻actsurj3

open ℱactsurj3 ⦃ … ⦄ public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔄)
  ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄
  ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔅 ⦄
  {ℓ} ⦃ _ : ∀ {x} → HasEquivalence (𝔅 x) ℓ ⦄
  where
  𝓯actsurj3 = 𝒻actsurj3 ([𝒻actsurj3] _∼ᵣ_ 𝔅)
  [𝓕actsurj3] = [ℱactsurj3] ([𝒻actsurj3] _∼ᵣ_ 𝔅)
  𝓕actsurj3 = ℱactsurj3 ([𝒻actsurj3] _∼ᵣ_ 𝔅)
