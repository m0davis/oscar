
open import Oscar.Prelude
open import Oscar.Data.¶
open import Oscar.Data.Descender
open import Oscar.Data.Fin
open import Oscar.Data.Term

module Oscar.Data.Substitist where

module Substitist {𝔭} (𝔓 : Ø 𝔭) where

  open Term 𝔓

  Substitist = flip Descender⟨ (λ n-o → Fin (↑ n-o) × Term n-o) ⟩
