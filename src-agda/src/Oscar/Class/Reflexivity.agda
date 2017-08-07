
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  𝔯eflexivity : ℭlass _∼_
  𝔯eflexivity = ∁ ∀ {x} → x ∼ x
  open ℭlass 𝔯eflexivity using () renaming (SET-METHOD to 𝓻eflexivity; GET-CLASS to 𝓡eflexivity; GET-METHOD to reflexivity[_]) public
  open ℭlass 𝔯eflexivity using () renaming (GET-METHOD to ε[_]) public

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  open ℭlass (𝔯eflexivity _∼_) using () renaming (GET-METHOD to reflexivity) public
  open ℭlass (𝔯eflexivity _∼_) using () renaming (GET-METHOD to ε) public
