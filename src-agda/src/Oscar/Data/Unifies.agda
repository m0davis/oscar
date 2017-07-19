
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Class.Surjection

module Oscar.Data.Unifies where

𝓾nifies₀ : ∀
  {𝔵} {𝔒 : Ø 𝔵}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  {𝔯₁} (_↦₁_ : π̂² 𝔯₁ 𝔒)
  𝔯₂
  → Ø 𝔵 ∙̂ 𝔭 ∙̂ 𝔯₁ ∙̂ ↑̂ 𝔯₂
𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂ = ∀ {m} → 𝔓 m → 𝔓 m → Ṗroperty 𝔯₂ (m ↦₁_)

Unifies₀ : ∀
  {𝔵} {𝔒 : Ø 𝔵}
  {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  {𝔯₁} {_↦₁_ : π̂² 𝔯₁ 𝔒}
  ⦃ _ : [𝓢urjectivity] _↦₁_ (Extension 𝔓) ⦄
  ⦃ _ : 𝓢urjectivity _↦₁_ (Extension 𝔓) ⦄
  {𝔯₂} (_↦₂_ : ∀̇ π̂² 𝔯₂ 𝔓)
  → 𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂
Unifies₀ _↦₂_ p q .π₀ x =
  let _↦₂_ = _↦₂_
      infix 4 _↦₂_
  in
  x ◃ p ↦₂ x ◃ q

Unifies₀⟦_⟧ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  {ℓ} (_≈_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ)
  → 𝓾nifies₀ ℭ 𝔄 ℓ
Unifies₀⟦ _ ⟧ = Unifies₀

≡-Unifies₀ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  → 𝓾nifies₀ ℭ 𝔄 ∅̂
≡-Unifies₀ = Unifies₀ _≡_

≡-Unifies₀⟦_⟧ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  → 𝓾nifies₀ ℭ 𝔄 ∅̂
≡-Unifies₀⟦ _ ⟧ = ≡-Unifies₀

ExtensionalUnifies : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  (let _↦_ = Arrow 𝔄 𝔅)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  {ℓ₁} (_∼₁_ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓ₁)
  {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
  ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
  ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
  ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
  ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
  → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty ℓ₂ 𝔄 𝔅 _∼₁_ m
ExtensionalUnifies _ {_∼₂_ = _∼₂_} s t =
  Unifies₀ _∼₂_ s t , λ f≐g f◃s=f◃t →
    ⟪ f≐g ⟫[ Pointwise _∼₂_ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise _∼₂_ ] s)

≡-ExtensionalUnifies : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  (let _↦_ = Arrow 𝔄 𝔅)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
  ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
  ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
  ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
  ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
  → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty ℓ₂ 𝔄 𝔅 _≡_ m
≡-ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} {_∼₂_ = _∼₂_} s t = ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} _≡_ {_∼₂_ = _∼₂_} s t
