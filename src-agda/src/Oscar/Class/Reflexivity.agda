
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
  𝓻eflexivity : Set (𝔯 ∙̂ 𝔬)
  𝓻eflexivity = ∀ {x} → ℭlass.SET-METHOD (𝔯eflexivity _∼_ x)
  𝓡eflexivity : Set (𝔯 ∙̂ 𝔬)
  𝓡eflexivity = ∀ {x} → ℭlass.GET-CLASS (𝔯eflexivity _∼_ x)
  reflexivity[_] : {{ _ : 𝓡eflexivity }} → 𝓻eflexivity
  reflexivity[_] {x = x} = ℭlass.GET-METHOD (𝔯eflexivity _∼_ x)
  ε[_] = reflexivity[_]

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  where
  reflexivity : {{ _ : 𝓡eflexivity _∼_ }} → 𝓻eflexivity _∼_
  reflexivity {x = x} = ℭlass.GET-METHOD (𝔯eflexivity _∼_ x)
  ε = reflexivity
