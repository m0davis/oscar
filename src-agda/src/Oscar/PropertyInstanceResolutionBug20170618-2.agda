{-# OPTIONS --show-implicit #-}
module Oscar.PropertyInstanceResolutionBug20170618-2 where

open import Oscar.Prelude

module _ where

  postulate ¶ : Set

module _ where

  postulate ¶⟨<_⟩ : ¶ → Ø₀

  Fin = ¶⟨<_⟩

module _ where

  data Proposequality {𝔬} {𝔒 : Ø 𝔬} (𝓞 : 𝔒) : 𝔒 → Ø₀ where
    instance ∅ : Proposequality 𝓞 𝓞

  Proposequality⟦_⟧ : ∀ {𝔬} (𝔒 : Ø 𝔬) → 𝔒 → 𝔒 → Ø₀
  Proposequality⟦ _ ⟧ = Proposequality

  [Proposequality] : ∀ {𝔬} {𝔒 : Ø 𝔬} → {x y : 𝔒} → Ø₀
  [Proposequality] {x = x} {y = y} = Proposequality x y

module _ where

  infix 4 _≡_
  _≡_ = Proposequality

module _ where

  Proposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality 𝓟₁ 𝓟₂ = ∀ 𝓞 → Proposequality (𝓟₁ 𝓞) (𝓟₂ 𝓞)

  Proposextensequality⟦_⟧ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality⟦ _ ⟧ = Proposextensequality

  Proposextensequality[_/_] : ∀ {𝔬} (𝔒 : Ø 𝔬) {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality[ _ / _ ] = Proposextensequality

module _ where

  infix 4 _≡̇_
  _≡̇_ = Proposextensequality

module !Term {𝔭} (𝔓 : Ø 𝔭) where
-- module _ where

  data Term (n : ¶) : Ø 𝔭 where
  -- data Term (n : ¶) : Ø₀ where
    i : (x : ¶⟨< n ⟩) → Term n

-- module _ where
module !Substitunction {𝔭} (𝔓 : Ø 𝔭) where

  open !Term 𝔓

  Substitunction : ¶ → ¶ → Ø 𝔭
  -- Substitunction : ¶ → ¶ → Ø₀
  Substitunction m n = ¶⟨< m ⟩ → Term n

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

module IMPORT…Reflexivity where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓻eflexivity = ∀ {x} → x ∼ x
    record 𝓡eflexivity : Ø 𝔬 ∙̂ 𝔯 where
      field
        reflexivity : 𝓻eflexivity

  open 𝓡eflexivity ⦃ … ⦄ public renaming (reflexivity to ε)

open IMPORT…Reflexivity public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓼ymmetry = ∀ {x y} → x ∼ y → y ∼ x
    record 𝓢ymmetry : Ø 𝔬 ∙̂ 𝔯 where field symmetry : 𝓼ymmetry

  open 𝓢ymmetry ⦃ … ⦄ public

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

module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

    instance

      postulate
        𝓢ymmetryProposextensequality : 𝓢ymmetry Proposextensequality⟦ 𝔓 ⟧

module _ {𝔭} {𝔓 : Ø 𝔭} where
  open !Term 𝔓
  open !Substitunction 𝔓

record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
  constructor ∁
  no-eta-equality

  open !Substitunction 𝔓
  open !Term 𝔓

  instance

    postulate 𝓣ransitivitySubstitunction : 𝓣ransitivity Substitunction

postulate 𝔓 : Ø₀

--module _ {𝔭} {𝔓 : Ø 𝔭} where
module _ where
  open !Term 𝔓
  open !Substitunction 𝔓

  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ ∁)

  instance

    𝓡eflexivitySubstitunction : 𝓡eflexivity Substitunction
    𝓡eflexivitySubstitunction .𝓡eflexivity.reflexivity = i

    postulate
      [𝓣ransleftidentitySubstitunction] : [𝓣ransleftidentity] Substitunction Proposextensequality
      𝓣ransleftidentitySubstitunction : 𝓣ransleftidentity Substitunction Proposextensequality

postulate ≡̇-symmetry : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → 𝓼ymmetry Proposextensequality⟦ 𝔓 ⟧

module _ where

  open !Substitunction 𝔓
  open !Term 𝔓

  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ ∁)
{-
  prop-id0 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality) (let P₀ = π₀ P) → P₀ (i ∙ f) → P₀ f
  prop-id0 P = π₁ P (transleftidentity {_∼̇_ = Proposextensequality})

  prop-id1 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality[ Fin m / (λ _ → Term _) ]) (let P₀ = π₀ P) → P₀ f → P₀ (i ∙ f)
  prop-id1 P = π₁ P (symmetry (transleftidentity {_∼̇_ = Proposextensequality}))

  prop-id14 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality[ Fin m / (λ _ → Term _) ]) (let P₀ = π₀ P) → P₀ f → P₀ (i ∙ f)
  prop-id14 {m = m} {n} {f = f} P = π₁ P (symmetry {x = _} (transleftidentity {_∼̇_ = Proposextensequality}))
-}
  prop-id15 : ∀ {m n ℓ} {f : Substitunction m n} (P : 𝓔xtensionalProperty (Fin m) Term ℓ Proposextensequality[ Fin m / (λ _ → Term _) ]) (let P₀ = π₀ P) → P₀ f → P₀ (i ∙ f)
  prop-id15 {m = m} {n} {f = f} P = π₁ P (≡̇-symmetry {x = λ _ → 𝓣ransitivity.transitivity 𝓣ransitivitySubstitunction _ _ _} (transleftidentity {_∼̇_ = Proposextensequality}))
