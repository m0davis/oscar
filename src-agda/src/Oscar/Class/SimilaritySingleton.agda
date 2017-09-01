
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Unit

module Oscar.Class.SimilaritySingleton where

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
