
open import Oscar.Prelude
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity

module Oscar.Class.Transleftidentity where

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransleftidentity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : Reflexivity.class _∼_ ⦄
      ⦃ _ : Transitivity.class _∼_ ⦄
      where
      𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ∼̇ f
      record 𝓣ransleftidentity ⦃ _ : [𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transleftidentity : 𝓽ransleftidentity
  open 𝓣ransleftidentity ⦃ … ⦄ public

  transleftidentity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
    ⦃ _ : Reflexivity.class _∼_ ⦄
    ⦃ _ : Transitivity.class _∼_ ⦄
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    → 𝓽ransleftidentity _∼_ _∼̇_
  transleftidentity[ _ ] = transleftidentity

module _ where

  open import Oscar.Data.Proposequality

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔣} (F : 𝔒 → Ø 𝔣)
    {𝔱} (T : {x : 𝔒} → F x → 𝔒 → Ø 𝔱)
    (let _∼_ : ∀ x y → Ø 𝔣 ∙̂ 𝔱
         _∼_ = λ x y → (f : F x) → T f y)
    where
    record [≡̇-𝓣ransleftidentity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : Reflexivity.class _∼_ ⦄
      ⦃ _ : Transitivity.class _∼_ ⦄
      where
      ≡̇-𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ≡̇ f
      record ≡̇-𝓣ransleftidentity ⦃ _ : [≡̇-𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔣 ∙̂ 𝔱 where field ≡̇-transleftidentity : ≡̇-𝓽ransleftidentity
  open ≡̇-𝓣ransleftidentity ⦃ … ⦄ public

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔣} {F : 𝔒 → Ø 𝔣}
    {𝔱} {T : {x : 𝔒} → F x → 𝔒 → Ø 𝔱}
    (let _∼_ : ∀ x y → Ø 𝔣 ∙̂ 𝔱
         _∼_ = λ x y → (f : F x) → T f y)
    where
    instance
      `[≡̇-𝓣ransleftidentity] :
        ⦃ _ : [𝓣ransleftidentity] _∼_ _≡̇_ ⦄
        → [≡̇-𝓣ransleftidentity] F T
      `[≡̇-𝓣ransleftidentity] = ∁

      `≡̇-𝓣ransleftidentity :
        ⦃ _ : [𝓣ransleftidentity] _∼_ _≡̇_ ⦄
        ⦃ _ : Reflexivity.class _∼_ ⦄
        ⦃ _ : Transitivity.class _∼_ ⦄
        ⦃ _ : 𝓣ransleftidentity _∼_ _≡̇_ ⦄
        → ≡̇-𝓣ransleftidentity F T
      `≡̇-𝓣ransleftidentity .≡̇-𝓣ransleftidentity.≡̇-transleftidentity = transleftidentity
