
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

module Reflexivity'
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  (x : 𝔒)
  = ℭLASS (_∼_) (x ∼ x)

module Reflexivity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  class = ∀ {x} → Reflexivity'.class _∼_ x
  type = ∀ {x} → Reflexivity'.type _∼_ x
  method : ⦃ _ : class ⦄ → type
  method = Reflexivity'.method _∼_ _

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  reflexivity = Reflexivity.method _∼_
  ε = reflexivity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  reflexivity[_] = Reflexivity.method _∼_
  ε[_] = reflexivity
