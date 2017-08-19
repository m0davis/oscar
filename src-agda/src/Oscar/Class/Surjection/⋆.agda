
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection

module Oscar.Class.Surjection.⋆ where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : Surjection.class 𝔒 𝔒
    𝓢urjectionIdentity .⋆ = ¡
