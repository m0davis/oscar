
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Reflexivity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  (x : 𝔒)
  where
  𝔯eflexivity : ℭlass {𝔯} _∼_
  𝔯eflexivity = ∁ $′ x ∼ x

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  private
    module _
      (x : 𝔒)
      where
      open ℭlass (𝔯eflexivity _∼_ x) public
  𝓡eflexivity = ∀ {x} → GET-CLASS x
  𝓻eflexivity = ∀ {x} → SET-METHOD x
  reflexivity[_] = λ ⦃ _ : 𝓡eflexivity ⦄ {x} → GET-METHOD x
  ε[_] = λ ⦃ _ : 𝓡eflexivity ⦄ {x} → GET-METHOD x

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  reflexivity = reflexivity[ _∼_ ]
  ε = reflexivity
