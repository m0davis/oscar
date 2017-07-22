
open import Oscar.Prelude

module Oscar.Class.Surjection where -- FIXME Is it odd that here there should be an instance whereas in all other Oscar.Class.* modules, there are (only?) classes; Perhaps all instances should be in a separate tree, e.g. Oscar.Instance.Surjection, Oscar.Instance.Reflexivity.Function, Oscar.Instance.Congruity.Proposequality.

module _ where

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    where
    module _
      where
      𝓼urjection = 𝔒₁ → 𝔒₂
      record 𝓢urjection : Ø 𝔬₁ ∙̂ 𝔬₂ where
        constructor ∁
        field surjection : 𝓼urjection
  open 𝓢urjection ⦃ … ⦄ public

  surjection[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    → 𝓼urjection 𝔒₁ 𝔒₂
  surjection[ _ ] = surjection

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡
