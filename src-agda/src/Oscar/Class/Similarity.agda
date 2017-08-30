
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.Similarity where

module SimilaritySingleton
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  (∼₁ : Ø 𝔞̇)
  (_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇) (let _∼₂_ = _∼₂_; infix 4 _∼₂_)
  (_◃_ : 𝔉 → 𝔄 → 𝔅) (let _◃_ = _◃_; infix 16 _◃_)
  (x y : 𝔄)
  (f : 𝔉)
  = ℭLASS (_◃_ , _∼₂_ , x , y) (∼₁ → f ◃ x ∼₂ f ◃ y)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {𝔣} {𝔉 : Ø 𝔣}
  {𝔞̇ 𝔟̇}
  {∼₁ : Ø 𝔞̇}
  {_∼₂_ : 𝔅 → 𝔅 → Ø 𝔟̇} (let _∼₂_ = _∼₂_; infix 4 _∼₂_)
  {_◃_ : 𝔉 → 𝔄 → 𝔅} (let _◃_ = _◃_; infix 16 _◃_)
  {x y : 𝔄}
  {f : 𝔉}
  where
  similaritySingleton = SimilaritySingleton.method ∼₁ _∼₂_ _◃_ x y f
  module _ ⦃ _ : SimilaritySingleton.class ∼₁ _∼₂_ _◃_ x y f ⦄ where
    instance
      toUnit : Unit.class (∼₁ → f ◃ x ∼₂ f ◃ y)
      toUnit .⋆ = similaritySingleton

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
  module _ ⦃ _ : Similarity.class _∼₁_ _∼₂_ _◃_ ⦄ where
    instance
      toSimilaritySingleton : ∀ {x y f} → SimilaritySingleton.class (x ∼₁ y) _∼₂_ _◃_ x y f
      toSimilaritySingleton .⋆ = similarity _
      toSimilarityM : ∀ {x y} → SimilarityM.class _∼₁_ _∼₂_ _◃_ x y
      toSimilarityM .⋆ = similarity
