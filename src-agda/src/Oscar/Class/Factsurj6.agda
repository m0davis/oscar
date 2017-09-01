
open import Oscar.Prelude
open import Oscar.Class.Similarity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjection

module Oscar.Class.Factsurj6 where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔭} (𝔓 : 𝔒₂ → Ø 𝔭)
  {𝔯} (_∼_ : 𝔒₁ → 𝔒₁ → Ø 𝔯)
  {ℓ∼} (_≈̈_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ∼) (let _≈̈_ = _≈̈_ ; infix 4 _≈̈_)
  {ℓ𝔭} (_≈̇_ : ∀ {x} → 𝔓 x → 𝔓 x → Ø ℓ𝔭) (let _≈̇_ = _≈̇_ ; infix 4 _≈̇_)
  where
  module _
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : Surjectextensivity.class _∼_ 𝔓 ⦄
    where
    𝓕actsurj6 = ∀ {m n} → Similarity.class (_≈̈_ {m} {n}) (_≈̇_ {surjection n}) ((flip _◃_))
