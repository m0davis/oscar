
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Transitivity

module Oscar.Class.Surjtranscommutativity where

module Surjtranscommutativity
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  (smap : Smap.type _∼₁_ _∼₂_ surjection surjection)
  (transitivity₁ : Transitivity.type _∼₁_)
  (let infixr 9 _∙₁_
       _∙₁_ : FlipTransitivity.type _∼₁_
       _∙₁_ g f = transitivity₁ f g)
  (transitivity₂ : Transitivity.type _∼₂_)
  (let infixr 9 _∙₂_
       _∙₂_ : FlipTransitivity.type _∼₂_
       _∙₂_ g f = transitivity₂ f g)
  = ℭLASS (_∼₁_ ,, _∼₂_ ,, (λ {x y} → _∼̇₂_ {x} {y}) ,, surjection ,, (λ {x y} → smap {x} {y}) ,, (λ {x y z} → transitivity₁ {x} {y} {z}) ,, (λ {x y z} → transitivity₂ {x} {y} {z})) (∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → smap (g ∙₁ f) ∼̇₂ smap g ∙₂ smap f)

module Surjtranscommutativity!
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  ⦃ I1 : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ I2 : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ I3 : Transitivity.class _∼₁_ ⦄
  ⦃ I4 : Transitivity.class _∼₂_ ⦄
  = Surjtranscommutativity (_∼₁_) (_∼₂_) (λ {x y} → _∼̇₂_ {x} {y}) smap transitivity transitivity

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  {smap : Smap.type _∼₁_ _∼₂_ surjection surjection}
  {transitivity₁ : Transitivity.type _∼₁_}
  {transitivity₂ : Transitivity.type _∼₂_}
  where
  surjtranscommutativity = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ∁ surjection ⦄ ⦃ ∁ (λ _ _ → smap) ⦄ ⦃ ∁ transitivity₁ ⦄ ⦃ ∁ transitivity₂ ⦄
  ⟪∙⟫-surjtranscommutativity-syntax = surjtranscommutativity
  syntax ⟪∙⟫-surjtranscommutativity-syntax f g = g ⟪∙⟫ f

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  where
  surjtranscommutativity! = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄
  ⟪∙⟫!-surjtranscommutativity-syntax = surjtranscommutativity!
  syntax ⟪∙⟫!-surjtranscommutativity-syntax f g = g ⟪∙⟫! f

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  {smap : Smap.type _∼₁_ _∼₂_ surjection surjection}
  {transitivity₁ : Transitivity.type _∼₁_}
  {transitivity₂ : Transitivity.type _∼₂_}
  where
  surjtranscommutativity[_] = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ∁ surjection ⦄ ⦃ ∁ (λ _ _ → smap) ⦄ ⦃ ∁ transitivity₁ ⦄ ⦃ ∁ transitivity₂ ⦄
  ⟪∙⟫-surjtranscommutativity[]-syntax = surjtranscommutativity[_]
  syntax ⟪∙⟫-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫[ t ] f

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  where
  surjtranscommutativity![_] = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄
  ⟪∙⟫!-surjtranscommutativity[]-syntax = surjtranscommutativity![_]
  syntax ⟪∙⟫!-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫![ t ] f
