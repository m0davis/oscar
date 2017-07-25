
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Class.Surjection
import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Data.ExtensionṖroperty
import Oscar.Class.Surjection
import Oscar.Data.ExtensionṖroperty
import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Class.Properthing.Ṗroperty
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Property.Setoid.ProductIndexEquivalence
import Oscar.Data.ExtensionṖroperty
import Oscar.Data.ProperlyExtensionNothing
import Oscar.Class.Properthing.ExtensionṖroperty

module Oscar.Data.Unifies where

𝓾nifies₀ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
  {𝔞} (𝔄 : π̂² 𝔞 𝔛)
  𝔟̇
  → Ø 𝔵 ∙̂ 𝔟 ∙̂ 𝔞 ∙̂ ↑̂ 𝔟̇
𝓾nifies₀ 𝔅 𝔄 𝔟̇ = ∀ {m} → 𝔅 m → 𝔅 m → Ṗroperty 𝔟̇ (𝔄 m)

Unifies₀ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : π̂² 𝔞 𝔛}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {𝔟̇} (𝔅̇ : ∀̇ π̂² 𝔟̇ 𝔅)
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  → 𝓾nifies₀ 𝔅 𝔄 𝔟̇
Unifies₀ 𝔅̇ p q .π₀ x =
  let _⟿_ = 𝔅̇
      infix 4 _⟿_
  in
  x ◃ p ⟿ x ◃ q

module Surjcollation
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  (ℬ̇ : ∀ 𝔟̇ {𝔟} → (𝔛 → Ø 𝔟) → Ø 𝔵 ∙̂ 𝔟 ∙̂ ↑̂ 𝔟̇)
  (𝔅̇ : ∀ {𝔟̇ 𝔟} {𝔅 : 𝔛 → Ø 𝔟} ⦃ _ : ℬ̇ 𝔟̇ 𝔅 ⦄ → ∀ {x} → 𝔅 x → 𝔅 x → Ø 𝔟̇)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {ℓ}
  (let ℭ : 𝔛 → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
       ℭ = LeftṖroperty ℓ 𝔄)
  ⦃ _ : ℬ̇ ℓ 𝔅 ⦄
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  where
  infix 18 _∼_
  _∼_ : ∀ {m} → 𝔅 m → 𝔅 m → ℭ m
  _∼_ = Unifies₀ 𝔅̇

SymUnifies₀ : ∀
  {𝔵} {𝔒 : Ø 𝔵}
  {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  {𝔯₁} {_↦₁_ : π̂² 𝔯₁ 𝔒}
  ⦃ _ : [𝓢urjectivity] _↦₁_ (Extension 𝔓) ⦄
  ⦃ _ : 𝓢urjectivity _↦₁_ (Extension 𝔓) ⦄
  {𝔯₂} (_↦₂_ : ∀̇ π̂² 𝔯₂ 𝔓)
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_↦₂_ {y}) ⦄
  → 𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂
SymUnifies₀ _↦₂_ = Unifies₀ _↦₂_

Unifies₀⟦_⟧ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  {𝔟̇} (𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø 𝔟̇)
  → 𝓾nifies₀ 𝔅 𝔄 𝔟̇
Unifies₀⟦ 𝔄 ⟧ 𝔅̇ = Unifies₀ 𝔅̇

SymUnifies₀⟦_⟧ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  {ℓ} (_≈_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ)
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_≈_ {y}) ⦄
  → 𝓾nifies₀ ℭ 𝔄 ℓ
SymUnifies₀⟦ _ ⟧ = SymUnifies₀

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

≡-SymUnifies₀⟦_⟧ : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  ⦃ _ : ∀ {y} → 𝓢ymmetry (Proposequality⟦ ℭ y ⟧) ⦄
  → 𝓾nifies₀ ℭ 𝔄 ∅̂
≡-SymUnifies₀⟦ _ ⟧ = SymUnifies₀ _≡_

ExtensionalUnifies : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  (let _↦_ = Arrow 𝔄 𝔅)
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  {ℓ₁} (_↦̇_ : ∀ {x y} → x ↦ y → x ↦ y → Ø ℓ₁)
  {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
  ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
  ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
  ⦃ _ : [𝓢urjextensionality] _↦_ _↦̇_ (Extension ℭ) (Pointwise _∼₂_) ⦄
  ⦃ _ : 𝓢urjextensionality _↦_ _↦̇_ (Extension ℭ) (Pointwise _∼₂_) ⦄
  → ∀ {m} → ℭ m → ℭ m → LeftExtensionṖroperty ℓ₂ _↦_ _↦̇_ m
ExtensionalUnifies _ {_∼₂_ = _∼₂_} s t =
  Unifies₀ _∼₂_ s t , λ f≐g f◃s=f◃t →
    ⟪ f≐g ⟫[ Pointwise _∼₂_ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise _∼₂_ ] s)
module Surjextenscollation
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞₁} {𝔄₁ : 𝔛 → Ø 𝔞₁}
  {𝔞₂} {𝔄₂ : 𝔛 → Ø 𝔞₂}
  (𝔄 : 𝔛 → 𝔛 → Ø 𝔞₁ ∙̂ 𝔞₂)
  ⦃ _ : 𝔄 ≡ Arrow 𝔄₁ 𝔄₂ ⦄
  (let 𝔄 : 𝔛 → 𝔛 → Ø 𝔞₁ ∙̂ 𝔞₂
       𝔄 = Arrow 𝔄₁ 𝔄₂)
  {ℓᵃ²} (𝔄̇₂ : ∀ {y} → 𝔄₂ y → 𝔄₂ y → Ø ℓᵃ²)
  (let 𝔄̇ : ∀ {x y} → 𝔄 x y → 𝔄 x y → Ø 𝔞₁ ∙̂ ℓᵃ²
       𝔄̇ {x} {y} = Pointwise 𝔄̇₂)
  {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
  {ℓᵇ}
  (let ℭ : 𝔛 → Ø 𝔵 ∙̂ 𝔞₁ ∙̂ 𝔞₂ ∙̂ ℓᵃ² ∙̂ ↑̂ ℓᵇ
       ℭ = LeftExtensionṖroperty ℓᵇ 𝔄 𝔄̇)
  {𝔅̇ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓᵇ}
  ⦃ _ : ∀ {y} → 𝓢ymmetry (𝔅̇ {y}) ⦄
  ⦃ _ : ∀ {y} → 𝓣ransitivity (𝔅̇ {y}) ⦄
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension 𝔅) ⦄
  ⦃ _ : [𝓢urjextensionality] 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  ⦃ _ : 𝓢urjextensionality 𝔄 𝔄̇ (Extension 𝔅) (Pointwise 𝔅̇) ⦄
  where

  infix 18 _∼_
  _∼_ : ∀ {m} → 𝔅 m → 𝔅 m → ℭ m
  _∼_ = ExtensionalUnifies 𝔄̇ -- FIXME was this better? ≡-ExtensionalUnifies {_∼₂_ = 𝔅̇}

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
≡-ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} {_∼₂_ = _∼₂_} s t = ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} (Pointwise _≡_) {_∼₂_ = _∼₂_} s t
