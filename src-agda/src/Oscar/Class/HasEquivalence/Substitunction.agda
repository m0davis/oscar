
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Property.Setoid.Proposextensequality

module Oscar.Class.HasEquivalence.Substitunction where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓

  instance

    HasEquivalenceSubstitunction : ∀ {x y} → HasEquivalence (Substitunction x y) _
    HasEquivalenceSubstitunction = ∁ Proposextensequality
