
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Leftstar where

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  where
  module 𝔏eftstar
    (𝔄̇ : 𝔄 → Ø 𝔞̇)
    (𝔅̇ : 𝔅 → Ø 𝔟̇)
    (_◂_ : 𝔉 → 𝔄 → 𝔅)
    where
    SET-METHOD : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇
    SET-METHOD = ∀ {x} f → 𝔄̇ x → 𝔅̇ (f ◂ x)
    record SET-CLASS
      ⦃ _ : Constraint _◂_ ⦄
      : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇
      where
      field ⋆ : SET-METHOD
    open SET-CLASS public
    GET-CLASS : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇
    GET-CLASS = SET-CLASS
    GET-METHOD : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
    GET-METHOD ⦃ ⌶ ⦄ = ⋆ ⌶
  module _
    (𝔄̇ : 𝔄 → Ø 𝔞̇)
    (𝔅̇ : 𝔅 → Ø 𝔟̇)
    (_◂_ : 𝔉 → 𝔄 → 𝔅)
    where
    open 𝔏eftstar 𝔄̇ 𝔅̇ _◂_
    Leftstar = GET-CLASS
    leftstar⟦_/_/_⟧ = GET-METHOD
  module _
    {𝔄̇ : 𝔄 → Ø 𝔞̇}
    {𝔅̇ : 𝔅 → Ø 𝔟̇}
    {_◂_ : 𝔉 → 𝔄 → 𝔅}
    where
    open 𝔏eftstar 𝔄̇ 𝔅̇ _◂_
    leftstar = GET-METHOD
