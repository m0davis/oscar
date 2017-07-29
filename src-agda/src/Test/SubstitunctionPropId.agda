
open import Oscar.Prelude
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
import Oscar.Class.PropId
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity
open import Oscar.Class.PropId
open import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Property.Setoid.Proposextensequality

module Test.SubstitunctionPropId {𝔭} (𝔓 : Ø 𝔭) where

open Substitunction 𝔓

prop-id-Substitunction : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
prop-id-Substitunction = prop-id
