
open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Symmetry

module Oscar.Class.PropId where

open import Oscar.Class

module Relpropid
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔯} (ℜ : 𝔛 → 𝔛 → Ø 𝔯)
  (transitivity : 𝓽ransitivity ℜ)
  (reflexivity : 𝓻eflexivity ℜ)
  {𝔭} (𝔓 : 𝔛 → Ø 𝔭)
  {𝔭𝔯} (pr : ∀ {m n} → 𝔓 m → ℜ m n → Ø 𝔭𝔯)
  = ℭLASS (ℜ ,, (λ {x y z} → transitivity {x} {y} {z}) ,, λ {x} → reflexivity {x})
          (∀ {m n} {f : ℜ m n} (P : 𝔓 m)
           → pr P f → pr P (transitivity f reflexivity))

instance
  RelpropidFromTransleftidentity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    {ℓ}
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    → Relpropid.class _∼_ transitivity reflexivity (LeftExtensionṖroperty ℓ _∼_ _∼̇_) (λ P f → π₀ (π₀ P) f)
  RelpropidFromTransleftidentity .⋆ (_ , P₁) = P₁ $ symmetry transleftidentity

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
  (let _∼_ = Arrow 𝔄 𝔅) (let infix 4 _∼_ ; _∼_ = _∼_)
  {ℓ̇} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇)
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  ⦃ _ : 𝓡eflexivity _∼_ ⦄
  ℓ
  where
  𝓹rop-id = ∀ {m n} {f : m ∼ n} (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m)
            (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
  record PropId : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ℓ̇ ∙̂ ↑̂ ℓ where field prop-id : 𝓹rop-id

open PropId ⦃ … ⦄ public

instance
  PropIdFromTransleftidentity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    {ℓ}
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    → PropId 𝔄 𝔅 _∼̇_ ℓ
  PropIdFromTransleftidentity .PropId.prop-id (_ , P₁) = P₁ $ symmetry transleftidentity
