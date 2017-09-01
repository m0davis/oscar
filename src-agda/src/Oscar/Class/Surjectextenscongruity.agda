
open import Oscar.Class.Similarity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjection
open import Oscar.Prelude

module Oscar.Class.Surjectextenscongruity where

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : π̂² 𝔯 𝔛₁)
  {𝔭} (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭̇} (𝔓̇ : ∀̇ π̂² 𝔭̇ (𝔓 ∘ surjection))
  ⦃ _ : Surjectextensivity.class ℜ 𝔓 ⦄
  where
  𝓢urjectextenscongruity = ∀ {m n} → Similarity.class (𝔓̇ {m}) (𝔓̇ {n}) _◃_

module Smaparrowleftsimilarity
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : π̂² 𝔯 𝔛₁)
  {𝔭₁} (𝔓₁ : π̂ 𝔭₁ 𝔛₂)
  {𝔭₂} (𝔓₂ : π̂ 𝔭₂ 𝔛₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭̇₁} (𝔓̇₁ : ∀̇ π̂² 𝔭̇₁ (𝔓₁ ∘ surjection))
  {𝔭̇₂} (𝔓̇₂ : ∀̇ π̂² 𝔭̇₂ (𝔓₂ ∘ surjection))
  ⦃ _ : Smaparrow.class ℜ 𝔓₁ 𝔓₂ surjection ⦄
  where
  class = ∀ {m n} → Similarity.class (𝔓̇₁ {m}) (𝔓̇₂ {n}) smaparrow
