
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private module M (x : 𝔒) = ℭLASS (mkClass _∼_ (x ∼ x))
  𝓡eflexivity = ∀ {x} → M.class x
  𝓻eflexivity = ∀ {x} → M.type x
  reflexivity[_] : ⦃ _ : 𝓡eflexivity ⦄ → 𝓻eflexivity
  reflexivity[_] = M.method _
  ε[_] = reflexivity[_]

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  reflexivity = reflexivity[ _∼_ ]
  ε = reflexivity
