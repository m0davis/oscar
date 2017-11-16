
open import Everything

module Test.SubstitunctionPropId {𝔭} (𝔓 : Ø 𝔭) where

open Substitunction 𝔓

relpropid-Substitunction : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
relpropid-Substitunction P pf = hmap _ P pf
