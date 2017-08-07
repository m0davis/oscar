
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Transitivity

module Oscar.Class.Surjtranscommutativity where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : 𝒮urjectivity! _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
  where
  𝔰urjtranscommutativity : ℭlass $ (λ {x y} → _∼̇₂_ {x} {y}) , (λ {x y z} → transitivity[ _∼₁_ ] {x} {y} {z}) , (λ {x y z} → transitivity[ _∼₁_ ] {x} {y} {z})
  𝔰urjtranscommutativity = ∁ ∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → surjectivity (g ∙ f) ∼̇₂ surjectivity g ∙ surjectivity f
  open ℭlass 𝔰urjtranscommutativity using () renaming (SET-METHOD to 𝓼urjtranscommutativity; GET-CLASS to 𝓢urjtranscommutativity) public

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : 𝒮urjectivity! _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
  where
  open ℭlass (𝔰urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_) using () renaming (GET-METHOD to surjtranscommutativity) public
  ⟪∙⟫-surjtranscommutativity-syntax = surjtranscommutativity
  syntax ⟪∙⟫-surjtranscommutativity-syntax f g = g ⟪∙⟫ f

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : 𝒮urjectivity! _∼₁_ _∼₂_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
  ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
  where
  open ℭlass (𝔰urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_) using () renaming (GET-METHOD to surjtranscommutativity[_]) public
  ⟪∙⟫-surjtranscommutativity[]-syntax = surjtranscommutativity[_]
  syntax ⟪∙⟫-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫[ t ] f
