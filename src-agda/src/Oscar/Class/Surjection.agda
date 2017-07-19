
open import Oscar.Prelude
open import Oscar.Class -- FIXME Include 𝓢urjection in the below module so that it may be imported into Class (rather than vice-versa)

module Oscar.Class.Surjection where -- FIXME Is it odd that here there should be an instance whereas in all other Oscar.Class.* modules, there are (only?) classes; Perhaps all instances should be in a separate tree, e.g. Oscar.Instance.Surjection, Oscar.Instance.Reflexivity.Function, Oscar.Instance.Congruity.Proposequality.

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡
