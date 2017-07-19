
open import Oscar.Prelude

module Oscar.Class.Transitivity where

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

  transitivity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_⊸_ : 𝔒 → 𝔒 → Ø 𝔯)
    ⦃ _ : 𝓣ransitivity _⊸_ ⦄
    → 𝓽ransitivity _⊸_
  transitivity[ _ ] = transitivity

  infixr 9 ∙[]-syntax
  ∙[]-syntax = transitivity[_]
  syntax ∙[]-syntax _⊸_ f g = g ∙[ _⊸_ ] f

  open import Oscar.Data

  ≡̇-transitivity : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
    ⦃ _ : 𝓣ransitivity (Proposextensequality⟦ 𝔓 ⟧) ⦄
    → 𝓽ransitivity Proposextensequality⟦ 𝔓 ⟧
  ≡̇-transitivity = transitivity[ Proposextensequality ]

  infixr 9 ≡̇-transitivity
  syntax ≡̇-transitivity f g = g ≡̇-∙ f

  infixr 9 ≡̇-transitivity-syntax
  ≡̇-transitivity-syntax = ≡̇-transitivity
  syntax ≡̇-transitivity-syntax f g = g ⟨≡̇⟩ f
