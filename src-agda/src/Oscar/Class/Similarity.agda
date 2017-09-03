
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.SimilaritySingleton
open import Oscar.Class.SimilarityM

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
  module _ ⦃ _ : Similarity.class _∼₁_ _∼₂_ _◃_ ⦄ where
    instance
      toSimilaritySingleton : ∀ {x y f} → SimilaritySingleton.class (x ∼₁ y) _∼₂_ _◃_ x y f
      toSimilaritySingleton .⋆ = similarity _
      toSimilarityM : ∀ {x y} → SimilarityM.class _∼₁_ _∼₂_ _◃_ x y
      toSimilarityM .⋆ = similarity

open import Oscar.Class.Smap
open import Oscar.Class.Surjection

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔭} (𝔓 : 𝔛₂ → Ø 𝔭)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇} (𝔓̇ : ∀ {x} → 𝔓 x → 𝔓 x → Ø 𝔭̇)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  where
  𝓕actsurj6 = ∀ {m n} → Similarity.class (ℜ̇ {m} {n}) (𝔓̇ {surjection n}) (flip _◃_)

module Smaparrowrightsimilarity
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔭₁} (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  {𝔭₂} (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  {𝔯} (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  {𝔯̇} (ℜ̇ : ∀ {x y} → ℜ x y → ℜ x y → Ø 𝔯̇)
  {𝔭̇₂} (𝔓̇₂ : ∀ {x} → 𝔓₂ x → 𝔓₂ x → Ø 𝔭̇₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  (smaparrow : Smaparrow.type ℜ 𝔓₁ 𝔓₂ surjection)
  where
  class = ∀ {m n} → Similarity.class (ℜ̇ {m} {n}) (𝔓̇₂ {surjection n}) (flip smaparrow)

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : π̂² 𝔯 𝔛₁)
  {𝔭} (𝔓 : π̂ 𝔭 𝔛₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭̇} (𝔓̇ : ∀̇ π̂² 𝔭̇ (𝔓 ∘ surjection))
  ⦃ _ : Smaphomarrow!.class ℜ 𝔓 ⦄
  where
  𝓢urjectextenscongruity = ∀ {m n} → Similarity.class (𝔓̇ {m}) (𝔓̇ {n}) _◃_

module SmaparrowleftsimilarityRaw
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : π̂² 𝔯 𝔛₁)
  {𝔭₁} (𝔓₁ : π̂ 𝔭₁ 𝔛₂)
  {𝔭₂} (𝔓₂ : π̂ 𝔭₂ 𝔛₂)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  {𝔭̇₁} (𝔓̇₁ : ∀̇ π̂² 𝔭̇₁ (𝔓₁ ∘ surjection))
  {𝔭̇₂} (𝔓̇₂ : ∀̇ π̂² 𝔭̇₂ (𝔓₂ ∘ surjection))
  (smaparrow : Smaparrow.type ℜ 𝔓₁ 𝔓₂ surjection)
  where
  class = ∀ {m n} → Similarity.class (𝔓̇₁ {m}) (𝔓̇₂ {n}) smaparrow

module Smaparrowleftsimilarity
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯} (ℜ : π̂² 𝔯 𝔛₁)
  {𝔭₁} (𝔓₁ : π̂ 𝔭₁ 𝔛₂)
  {𝔭₂} (𝔓₂ : π̂ 𝔭₂ 𝔛₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  {𝔭̇₁} (𝔓̇₁ : ∀̇ π̂² 𝔭̇₁ (𝔓₁ ∘ surjection))
  {𝔭̇₂} (𝔓̇₂ : ∀̇ π̂² 𝔭̇₂ (𝔓₂ ∘ surjection))
  ⦃ _ : Smaparrow.class ℜ 𝔓₁ 𝔓₂ surjection ⦄
  where
  class = ∀ {m n} → Similarity.class (𝔓̇₁ {m}) (𝔓̇₂ {n}) smaparrow
