
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical where

private

  module _
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    where
    module Visible
      (_∼_ : 𝔄 → 𝔄 → 𝔅)
      {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
      where
      𝓼ymmetrical = λ x y → (x ∼ y) ↦ (y ∼ x)
      𝓈ymmetrical = ∀ x y → 𝓼ymmetrical x y
      record 𝓢ymmetrical
        {𝓢 : 𝔄 → 𝔄 → Ø ℓ}
        ⦃ _ : 𝓢 ≡ 𝓼ymmetrical ⦄
        : Ø 𝔞 ∙̂ ℓ
        where
        field symmetrical : 𝓈ymmetrical -- FIXME might there be some reason to use "∀ x y → 𝓢 x y" here instead?
      Symmetrical : Ø _
      Symmetrical = 𝓢ymmetrical ⦃ ∅ ⦄
      symmetrical⟦_/_⟧ : ⦃ _ : Symmetrical ⦄ → 𝓈ymmetrical
      symmetrical⟦_/_⟧ ⦃ I ⦄ = 𝓢ymmetrical.symmetrical I
    module Hidden
      {_∼_ : 𝔄 → 𝔄 → 𝔅}
      {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
      where
      open Visible _∼_ _↦_
      symmetrical : ⦃ _ : Symmetrical ⦄ → 𝓈ymmetrical
      symmetrical = symmetrical⟦_/_⟧

open Visible public
open Hidden public
