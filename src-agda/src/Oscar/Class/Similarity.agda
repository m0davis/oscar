
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Similarity where

module Similarity
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  (_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇)
  (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇) (let _∼₂_ = _∼₂_; infix 4 _∼₂_)
  (_◃_ : 𝔉 → 𝔄 → 𝔅) (let _◃_ = _◃_; infix 16 _◃_)
  = ℭLASS (_◃_ , _∼₂_) (∀ {x y} f → x ∼₁ y → f ◃ x ∼₂ f ◃ y)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  {_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇}
  {_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇}
  {_◃_ : 𝔉 → 𝔄 → 𝔅}
  where
  similarity = Similarity.method _∼₁_ _∼₂_ _◃_
