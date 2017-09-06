
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Transitivity

module Oscar.Class.Surjtranscommutativity where

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
  = ℭLASS (_∼₁_ ,, _∼₂_ ,, λ {x y} → _∼̇₂_ {x} {y} ,, I1 ,, I2 ,, (λ {x y z f g} → I3 {x} {y} {z} {f} {g}) ,, (λ {x y z f g} → I4 {x} {y} {z} {f} {g})) (∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → smap (g ∙ f) ∼̇₂ smap g ∙ smap f)

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
  surjtranscommutativity = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ∁ surjection ⦄ ⦃ ∁ (λ _ _ → smap) ⦄ ⦃ λ {_ _ _ x∼y y∼z} → ∁ (transitivity₁ x∼y y∼z) ⦄ ⦃ λ {_ _ _ x∼y y∼z} → ∁ (transitivity₂ x∼y y∼z) ⦄
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
  surjtranscommutativity[_] = Surjtranscommutativity!.method _∼₁_ _∼₂_ _∼̇₂_ ⦃ ∁ surjection ⦄ ⦃ ∁ (λ _ _ → smap) ⦄ ⦃ λ {_ _ _ x∼y y∼z} → ∁ (transitivity₁ x∼y y∼z) ⦄ ⦃ λ {_ _ _ x∼y y∼z} → ∁ (transitivity₂ x∼y y∼z) ⦄
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
