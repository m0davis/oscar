
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftstar where

module Leftstar
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  = ℭLASS (_◂_ , 𝔅̇) (∀ {x} f → 𝔄̇ x → 𝔅̇ (f ◂ x))

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  {𝔄̇ : 𝔄 → Ø 𝔞̇}
  {𝔅̇ : 𝔅 → Ø 𝔟̇}
  {_◂_ : 𝔉 → 𝔄 → 𝔅}
  where
  leftstar = Leftstar.method 𝔄̇ 𝔅̇ _◂_

open import Oscar.Class.Surjection
open import Oscar.Class.Smap

module _
  {𝔞} {𝔄 : Ø 𝔞}
  ⦃ _ : Surjection.class 𝔄 𝔄 ⦄
  {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
  {𝔡} (𝔇 : ∀ {a} → 𝔅 (surjection a) → Ø 𝔡)
  ⦃ _ : Smaphomarrow!.class ℭ 𝔅 ⦄
  where
  𝓕actsurj4 = ∀ {a₁ a₂} → Leftstar.class (𝔇 {a₁}) (𝔇 {a₂}) (smaparrow {x = a₁} {a₂})
