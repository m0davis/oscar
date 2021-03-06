
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Transitivity where

module Transitivity'
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  x y z
  = ℭLASS (x ,, y ,, z ,, _∼_) (x ∼ y → y ∼ z → x ∼ z)

module Transitivity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  class = ∀ {x y z} → Transitivity'.class _∼_ x y z
  type = ∀ {x y z} → Transitivity'.type _∼_ x y z
  method : ⦃ _ : class ⦄ → type
  method {x = x} {y} {z} = Transitivity'.method _∼_ x y z

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  transitivity = Transitivity.method _∼_

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  ⦃ _ : Transitivity.class _∼_ ⦄
  where
  transitivity[_] = λ {x y z} (x∼y : x ∼ y) (y∼z : y ∼ z) → Transitivity.method _∼_ x∼y y∼z
  infixr 9 ∙[]-syntax
  ∙[]-syntax = transitivity[_]
  syntax ∙[]-syntax _⊸_ f g = g ∙[ _⊸_ ] f

module FlipTransitivity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  class = Transitivity.class _∼_
  type = ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
  method : ⦃ _ : class ⦄ → type
  method = flip transitivity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : Transitivity.class _∼_ ⦄
  where
  infixr 9 _∙_
  _∙_ : ∀ {x y z} (y∼z : y ∼ z) (x∼y : x ∼ y) → x ∼ z
  g ∙ f = transitivity f g

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  where

  open import Oscar.Data.Proposequality

  ≡̇-transitivity = transitivity[ Proposextensequality⟦ 𝔓 ⟧ ]

  infixr 9 ≡̇-transitivity
  syntax ≡̇-transitivity f g = g ≡̇-∙ f

  infixr 9 ≡̇-transitivity-syntax
  ≡̇-transitivity-syntax = ≡̇-transitivity
  syntax ≡̇-transitivity-syntax f g = g ⟨≡̇⟩ f
