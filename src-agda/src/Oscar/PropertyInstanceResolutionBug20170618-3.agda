{-# OPTIONS --show-implicit #-}
module Oscar.PropertyInstanceResolutionBug20170618-3 where

open import Oscar.Prelude

postulate
  ¶ : Set
  Fin : ¶ → Ø₀
  Term : ¶ → Ø₀
  Proposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬

Proposextensequality⟦_⟧ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
Proposextensequality⟦ _ ⟧ = Proposextensequality

Substitunction : ¶ → ¶ → Ø₀
Substitunction m n = Fin m → Term n

𝓟roperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
𝓟roperty 𝔒₁ 𝔒₂ ℓ = ∀ {y} → (𝔒₁ → 𝔒₂ y) → Ø ℓ

𝓔xtensional : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : Ø 𝔬₁)
  {𝔬₂} {𝔒₂ : 𝔛 → Ø 𝔬₂}
  {ℓ} → ∀ {ℓ̇} →
  (_↦_ : ∀ {y} → (𝔒₁ → 𝔒₂ y) → (𝔒₁ → 𝔒₂ y) → Ø ℓ̇)
  → 𝓟roperty 𝔒₁ 𝔒₂ ℓ
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ ∙̂ ℓ̇
𝓔xtensional 𝔒₁ {𝔒₂ = 𝔒₂} _↦_ P = ∀ {y} {f g : 𝔒₁ → 𝔒₂ y} → f ↦ g → P f → P g

𝓔xtensionalProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ → ∀ {ℓ̇} →
  (_↦_ : ∀ {y} → (𝔒₁ → 𝔒₂ y) → (𝔒₁ → 𝔒₂ y) → Ø ℓ̇)
  → Ø (𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇)
𝓔xtensionalProperty 𝔒₁ 𝔒₂ ℓ _↦_ = Σ (𝓟roperty 𝔒₁ 𝔒₂ ℓ) (𝓔xtensional 𝔒₁ _↦_)

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓻eflexivity = ∀ {x} → x ∼ x
    record 𝓡eflexivity : Ø 𝔬 ∙̂ 𝔯 where
      field
        reflexivity : 𝓻eflexivity

  open 𝓡eflexivity ⦃ … ⦄ public renaming (reflexivity to ε)

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓽ransitivity = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  record 𝓣ransitivity
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    : Ø 𝔬 ∙̂ 𝔯 where
    field transitivity : 𝓽ransitivity _∼_
    infixr 9 transitivity
    syntax transitivity f g = g ∙ f

  open 𝓣ransitivity ⦃ … ⦄ public

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
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ∼̇ f
      record 𝓣ransleftidentity ⦃ _ : [𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transleftidentity : 𝓽ransleftidentity
  open 𝓣ransleftidentity ⦃ … ⦄ public

record Substitunction⌶ : Ø₀ where
  constructor ∁
  no-eta-equality

  instance

    postulate 𝓣ransitivitySubstitunction : 𝓣ransitivity Substitunction

module _ where

  open Substitunction⌶ (Substitunction⌶ ∋ ∁)

  instance

    postulate
      𝓡eflexivitySubstitunction : 𝓡eflexivity Substitunction
      [𝓣ransleftidentitySubstitunction] : [𝓣ransleftidentity] Substitunction Proposextensequality
      𝓣ransleftidentitySubstitunction : 𝓣ransleftidentity Substitunction Proposextensequality

module _ where

postulate ≡̇-symmetry : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → ∀ {x y : (𝓞 : 𝔒) → 𝔓 𝓞} → Proposextensequality x y → Proposextensequality y x

module _ where

  open Substitunction⌶ (Substitunction⌶ ∋ ∁)

  prop-id0 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality) (let P₀ = π₀ P) → P₀ (ε ∙ f) → P₀ f
  prop-id0 P = π₁ P (transleftidentity {_∼̇_ = Proposextensequality})

  prop-id1 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality) (let P₀ = π₀ P) → P₀ f → P₀ (ε ∙ f)
  prop-id1 P = π₁ P (≡̇-symmetry (transleftidentity {_∼̇_ = Proposextensequality}))

  prop-id14 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ (λ {y''} → Proposextensequality {𝔒 = Fin m} {𝔓 = λ _ → Term y''})) (let P₀ = π₀ P) → P₀ f → P₀ (ε ∙ f)
  prop-id14 {f = f} P = π₁ P (≡̇-symmetry {x = _} (transleftidentity {_∼̇_ = Proposextensequality}))

  prop-id15 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality) (let P₀ = π₀ P) → P₀ f → P₀ (ε ∙ f)
  prop-id15 {f = f} P = π₁ P (≡̇-symmetry {x = ε ∙ f} (transleftidentity {_∼̇_ = Proposextensequality}))
