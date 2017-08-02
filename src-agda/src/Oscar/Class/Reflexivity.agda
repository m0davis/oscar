
open import Oscar.Prelude

module Oscar.Class.Reflexivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  𝓇eflexivity = λ x → x ∼ x
  𝓻eflexivity = ∀ {x} → 𝓇eflexivity x
  record 𝓡eflexivity : Ø 𝔬 ∙̂ 𝔯 where
    constructor ∁
    field
      reflexivity : 𝓻eflexivity

private

  module projection where

    open 𝓡eflexivity ⦃ … ⦄ public using (reflexivity)

    reflexivity[_] : ∀
      {𝔬} {𝔒 : Ø 𝔬}
      {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      → 𝓻eflexivity _∼_
    reflexivity[ _ ] = reflexivity

open projection public
open projection public using () renaming (reflexivity to ε; reflexivity[_] to ε[_])
