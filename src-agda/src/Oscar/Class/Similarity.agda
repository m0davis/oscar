
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Similarity where

private

  module _
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {𝔣} {𝔉 : Ø 𝔣}
    {𝔞̇ 𝔟̇}
    where
    module TCVisible
      (_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇)
      (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇)
      (_◂_ : 𝔉 → 𝔄 → 𝔅)
      where
      𝓼imilarity = λ x y f → x ∼₁ y → (f ◂ x) ∼₂ (f ◂ y)
      𝒮imilarity = ∀ {x y} f → 𝓼imilarity x y f
      record 𝓢imilarity
        ⦃ _ : Constraint _◂_ ⦄
        : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇ where
        field ⋆ : 𝒮imilarity
      Similarity : Ø _
      Similarity = 𝓢imilarity
      similarity⟦_/_/_⟧ : ⦃ _ : 𝓢imilarity ⦄ → 𝒮imilarity
      similarity⟦_/_/_⟧ ⦃ ⌶ ⦄ = 𝓢imilarity.⋆ ⌶
    module TCHidden
      {_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇}
      {_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇}
      {_◂_ : 𝔉 → 𝔄 → 𝔅}
      where
      open TCVisible _∼₁_ _∼₂_ _◂_
      similarity : ⦃ _ : Similarity ⦄ → 𝒮imilarity
      similarity = similarity⟦_/_/_⟧

open TCVisible public
open TCHidden public
