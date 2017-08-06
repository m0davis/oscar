
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Leftstar where

private

  record ℭlass
    {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
    {𝔄 : Ø 𝔞}
    {𝔅 : Ø 𝔟}
    {𝔉 : Ø 𝔣}
    (𝔄̇ : 𝔄 → Ø 𝔞̇)
    (𝔅̇ : 𝔅 → Ø 𝔟̇)
    (_◂_ : 𝔉 → 𝔄 → 𝔅)
    : Ø ↑̂ (𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇)
    where
    constructor ∁
    field
      SET-METHOD : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇
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

open ℭlass using (⋆) public

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  𝔩eftstar : ℭlass 𝔄̇ 𝔅̇ _◂_
  𝔩eftstar = ∁ ∀ {x} f → 𝔄̇ x → 𝔅̇ (f ◂ x)

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  open ℭlass (𝔩eftstar 𝔄̇ 𝔅̇ _◂_)
  Leftstar : Ø 𝔞 ∙̂ 𝔣 ∙̂ 𝔞̇ ∙̂ 𝔟̇
  Leftstar = GET-CLASS
  leftstar⟦_/_/_⟧ : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftstar⟦_/_/_⟧ = GET-METHOD
module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  {𝔄̇ : 𝔄 → Ø 𝔞̇}
  {𝔅̇ : 𝔅 → Ø 𝔟̇}
  {_◂_ : 𝔉 → 𝔄 → 𝔅}
  where
  open ℭlass (𝔩eftstar 𝔄̇ 𝔅̇ _◂_)
  leftstar : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftstar = GET-METHOD
