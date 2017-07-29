
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Data.Substitunction
open import Oscar.Data.Proposequality
import Oscar.Property.Setoid.Proposextensequality

module Oscar.Class.HasEquivalence.Substitunction where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓

  instance

    HasEquivalenceSubstitunction : ∀ {x y} → HasEquivalence (Substitunction x y) _
    HasEquivalenceSubstitunction = ∁ Proposextensequality
