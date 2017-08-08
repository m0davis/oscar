
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity

module Oscar.Class.Transextensionality where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  ⦃ tr : 𝓣ransitivity _∼_ ⦄
  where
  𝔱ransextensionality : ℭlass $ (λ {x y} → _∼̇_ {x} {y}) , tr -- (λ {x y z} → transitivity[ _∼_ ] {x} {y} {z}) ,
  𝔱ransextensionality = ∁ ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
  open ℭlass 𝔱ransextensionality using () renaming (GET-CLASS to 𝓣ransextensionality; SET-METHOD to 𝓽ransextensionality) public

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  where
  open ℭlass (𝔱ransextensionality _∼_ _∼̇_) using () renaming (GET-METHOD to transextensionality) public
