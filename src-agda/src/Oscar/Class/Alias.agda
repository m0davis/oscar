
module Oscar.Class.Alias where

open import Oscar.Prelude
open import Oscar.R
open import Oscar.Class

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔮}
    (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
  where
  𝓢ymmetry′ = 𝓢ymmetry 𝔔 𝔔
  𝓼ymmetry′ = 𝓼ymmetry 𝔔 𝔔
  Symmetry′ = Symmetry 𝔔 𝔔

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔮}
    (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
  where
  𝓣ransitivity′ = 𝓣ransitivity 𝔔 𝔔 𝔔  -- 𝓡₅ _ _ (λ x y → 𝔔 x y) _ (λ _ y _ z → 𝔔 y z) (λ x _ _ z _ → 𝔔 x z)
  𝓽ransitivity′ = 𝓽ransitivity 𝔔 𝔔 𝔔 -- ∀ {x y} → 𝔔 x y → ∀ {z} → 𝔔 y z → 𝔔 x z
  Transitivity′ = Transitivity 𝔔 𝔔 𝔔
  Transitivity′-I₁ = Transitivity-I₁ 𝔔 𝔔 𝔔
  Transitivity′-I₂ = Transitivity-I₂ 𝔔 𝔔 𝔔

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔮}
    (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
  where
  𝓒ongruity′ = 𝓒ongruity 𝔔 𝔔
  𝓬ongruity′ = 𝓬ongruity 𝔔 𝔔

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
  {𝔮}
    (𝔔 : ((o : 𝔒) → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → Ø 𝔮)
  where
  𝓒̇ongruity′ = 𝓒̇ongruity 𝔔 (λ F f₁ f₂ → 𝔔 (F ˢ f₁) (F ˢ f₂))
  𝓬̇ongruity′ = 𝓬̇ongruity 𝔔 (λ F f₁ f₂ → 𝔔 (F ˢ f₁) (F ˢ f₂))

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔪}
    (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
  {𝔮}
    (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
    (𝒯 : 𝓽ransitivity′ 𝔐)
  where
  𝓔xtensionality′ = 𝓔xtensionality 𝔐 𝔔 𝔔 (λ f₁ f₂ g₁ g₂ → 𝔔 (𝒯 f₁ g₁) (𝒯 f₂ g₂))
  𝓮xtensionality′ = 𝓮xtensionality 𝔐 𝔔 𝔔 (λ f₁ f₂ g₁ g₂ → 𝔔 (𝒯 f₁ g₁) (𝒯 f₂ g₂))
