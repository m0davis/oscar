
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

module Leftstar,smaparrow
  {𝔵₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  {𝔭₁ 𝔭₂} (𝔓₁ : 𝔛₂ → Ø 𝔭₁) (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭̇₁} (𝔓̇₁ : ∀ {a} → 𝔓₁ (surjection a) → Ø 𝔭̇₁)
  {𝔭̇₂} (𝔓̇₂ : ∀ {a} → 𝔓₂ (surjection a) → Ø 𝔭̇₂)
  (smaparrow : Smaparrow.type ℜ 𝔓₁ 𝔓₂ surjection)
  where
  class = ∀ {a₁ a₂} → Leftstar.class (𝔓̇₁ {a₁}) (𝔓̇₂ {a₂}) smaparrow
  type = ∀ {a₁ a₂} → Leftstar.type (𝔓̇₁ {a₁}) (𝔓̇₂ {a₂}) smaparrow

module Leftstar,smaparrow!
  {𝔵₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭₁ 𝔭₂} (𝔓₁ : 𝔛₂ → Ø 𝔭₁) (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭̇₁} (𝔓̇₁ : ∀ {a} → 𝔓₁ (surjection a) → Ø 𝔭̇₁)
  {𝔭̇₂} (𝔓̇₂ : ∀ {a} → 𝔓₂ (surjection a) → Ø 𝔭̇₂)
  ⦃ _ : Smaparrow!.class ℜ 𝔓₁ 𝔓₂ ⦄
  = Leftstar,smaparrow surjection 𝔓₁ 𝔓₂ ℜ 𝔓̇₁ 𝔓̇₂ smaparrow

module Leftstar,smaphomarrow
  {𝔵₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  {𝔭} (𝔓 : 𝔛₂ → Ø 𝔭)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭̇} (𝔓̇ : ∀ {a} → 𝔓 (surjection a) → Ø 𝔭̇)
  (smaparrow : Smaphomarrow.type ℜ 𝔓 surjection)
  = Leftstar,smaparrow surjection 𝔓 𝔓 ℜ 𝔓̇ 𝔓̇ smaparrow

module Leftstar,smaphomarrow!
  {𝔵₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭} (𝔓 : 𝔛₂ → Ø 𝔭)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔭̇} (𝔓̇ : ∀ {a} → 𝔓 (surjection a) → Ø 𝔭̇)
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  = Leftstar,smaphomarrow surjection 𝔓 ℜ 𝔓̇ smaparrow
