
module Oscar.Data where

open import Oscar.Prelude
open import Oscar.Data.Maybe public
open import Oscar.Data.ṖropertyEquivalence public
open import Oscar.Data.¶ public
open import Oscar.Data.List public
open import Oscar.Data.Fin public
open import Oscar.Data.Vec public
open import Oscar.Data.Descender public
open import Oscar.Data.𝟘 public
open import Oscar.Data.𝟙 public
open import Oscar.Data.𝟚 public
open import Oscar.Data.Proposequality public
open import Oscar.Data.Term public
open import Oscar.Data.Substitunction public

module Substitist {𝔭} (𝔓 : Ø 𝔭) where

  open Term 𝔓

  Substitist = flip Descender⟨ (λ n-o → Fin (↑ n-o) × Term n-o) ⟩

module _ where

  data Decidable {a} (A : Ø a) : Ø a where
    ↑_ : A → Decidable A
    ↓_ : ¬ A → Decidable A
