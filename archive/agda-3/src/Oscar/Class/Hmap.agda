
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Hmap where

module Hmap
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯₁} {𝔯₂}
  (ℜ₁ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁)
  (ℜ₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₂)
  = ℭLASS (ℜ₁ , ℜ₂)
          (∀ x y
           → ℜ₁ x y → ℜ₂ x y)

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯₁} {𝔯₂}
  {ℜ₁ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁}
  {ℜ₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₂}
  where
  hmap = Hmap.method ℜ₁ ℜ₂

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔯₁} {𝔯₂}
  {ℜ₁ : 𝔛 → 𝔛 → Ø 𝔯₁}
  {ℜ₂ : 𝔛 → 𝔛 → Ø 𝔯₂}
  where
  smap : ⦃ _ : Hmap.class ℜ₁ ℜ₂ ⦄ → ∀ {x y} → ℜ₁ x y → ℜ₂ x y
  smap = Hmap.method ℜ₁ ℜ₂ _ _
  § = smap

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔯₁} {𝔯₂}
  {ℜ₁ : 𝔛 → 𝔛 → Ø 𝔯₁}
  (ℜ₂ : 𝔛 → 𝔛 → Ø 𝔯₂)
  where
  smap[_] : ⦃ _ : Hmap.class ℜ₁ ℜ₂ ⦄ → ∀ {x y} → ℜ₁ x y → ℜ₂ x y
  smap[_] = Hmap.method ℜ₁ ℜ₂ _ _
  §[_] = smap[_]
