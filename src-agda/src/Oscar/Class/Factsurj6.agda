
open import Oscar.Prelude
open import Oscar.Class.Similarity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjection

module Oscar.Class.Factsurj6 where

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔭} (𝔓 : 𝔛₂ → Ø 𝔭)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇} (𝔓̇ : ∀ {x} → 𝔓 x → 𝔓 x → Ø 𝔭̇)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  where
  𝓕actsurj6 = ∀ {m n} → Similarity.class (ℜ̇ {m} {n}) (𝔓̇ {surjection n}) (flip _◃_)

module Smaparrowrightsimilarity
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔭₁} (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  {𝔭₂} (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇₂} (𝔓̇₂ : ∀ {x} → 𝔓₂ x → 𝔓₂ x → Ø 𝔭̇₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  (smaparrow : Smaparrow.type ℜ 𝔓₁ 𝔓₂ surjection)
  where
  class = ∀ {m n} → Similarity.class (ℜ̇ {m} {n}) (𝔓̇₂ {surjection n}) (flip smaparrow)
