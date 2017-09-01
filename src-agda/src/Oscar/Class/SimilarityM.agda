
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.SimilarityM where

module SimilarityM
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  (_∼₁_ : 𝔄 → 𝔄 → Ø 𝔞̇)
  (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇) (let _∼₂_ = _∼₂_; infix 4 _∼₂_)
  (_◃_ : 𝔉 → 𝔄 → 𝔅) (let _◃_ = _◃_; infix 16 _◃_)
  x y
  = ℭLASS (_◃_ , _∼₁_ , _∼₂_ , x , y) (∀ f → x ∼₁ y → f ◃ x ∼₂ f ◃ y)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  {∼₁ : 𝔄 → 𝔄 → Ø 𝔞̇}
  {∼₂ : 𝔅 → 𝔅 → Ø 𝔟̇}
  {◃ : 𝔉 → 𝔄 → 𝔅}
  {x y}
  where
  similarityM = SimilarityM.method ∼₁ ∼₂ ◃ x y
  instance SimilarityM--Unit : ⦃ _ : SimilarityM.class ∼₁ ∼₂ ◃ x y ⦄ → Unit.class (SimilarityM.type ∼₁ ∼₂ ◃ x y)
           SimilarityM--Unit .⋆ = similarityM
