
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Leftstar where

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  (𝔄̇ : 𝔄 → Ø 𝔞̇)
  (𝔅̇ : 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  𝔩eftstar : ℭlass (_◂_ , 𝔅̇)
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
  open ℭlass (𝔩eftstar 𝔄̇ 𝔅̇ _◂_) using () renaming (GET-CLASS to Leftstar; GET-METHOD to leftstar⟦_/_/_⟧) public

module _
  {𝔞 𝔟 𝔣 𝔞̇ 𝔟̇}
  {𝔄 : Ø 𝔞}
  {𝔅 : Ø 𝔟}
  {𝔉 : Ø 𝔣}
  {𝔄̇ : 𝔄 → Ø 𝔞̇}
  {𝔅̇ : 𝔅 → Ø 𝔟̇}
  {_◂_ : 𝔉 → 𝔄 → 𝔅}
  where
  open ℭlass (𝔩eftstar 𝔄̇ 𝔅̇ _◂_) using () renaming (GET-METHOD to leftstar) public
