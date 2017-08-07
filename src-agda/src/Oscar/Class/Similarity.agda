
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Similarity where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  (_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇)
  (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  𝔰imilarity : ℭlass (_◂_ , _∼₂_)
  𝔰imilarity = ∁ ∀ {x y} f → x ∼₁ y → (f ◂ x) ∼₂ (f ◂ y)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  (_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇)
  (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇)
  (_◂_ : 𝔉 → 𝔄 → 𝔅)
  where
  open ℭlass (𝔰imilarity _∼₁_ _∼₂_ _◂_) using () renaming (GET-CLASS to Similarity; GET-METHOD to similarity⟦_/_/_⟧) public

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  {_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇}
  {_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇}
  {_◂_ : 𝔉 → 𝔄 → 𝔅}
  where
  open ℭlass (𝔰imilarity _∼₁_ _∼₂_ _◂_) using () renaming (GET-METHOD to similarity) public
  module SIMILARITY = ℭlass (𝔰imilarity _∼₁_ _∼₂_ _◂_)
