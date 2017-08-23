
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjectivity
open import Oscar.Data.Fin
open import Oscar.Data.Term
open import Oscar.Data.Vec
import Oscar.Class.Surjection.⋆

module Oscar.Class.Surjectivity.ExtensionFinExtensionTerm where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Term 𝔓

  private

    mutual

      𝓼urjectivityExtensionFinExtensionTerm : Surjectivity!.TYPE (Extension Fin) (Extension Term)
      𝓼urjectivityExtensionFinExtensionTerm x (i y) = i (x y)
      𝓼urjectivityExtensionFinExtensionTerm x leaf = leaf
      𝓼urjectivityExtensionFinExtensionTerm x (l fork r) = 𝓼urjectivityExtensionFinExtensionTerm x l fork 𝓼urjectivityExtensionFinExtensionTerm x r
      𝓼urjectivityExtensionFinExtensionTerm x (function f ts) = function f $ 𝓼urjectivityExtensionFinExtensionTerms x ts

      𝓼urjectivityExtensionFinExtensionTerms : ∀ {N} → Surjectivity!.TYPE (Extension Fin) (Extension $ Terms N)
      𝓼urjectivityExtensionFinExtensionTerms x ∅ = ∅
      𝓼urjectivityExtensionFinExtensionTerms x (t , ts) = 𝓼urjectivityExtensionFinExtensionTerm x t , 𝓼urjectivityExtensionFinExtensionTerms x ts

  instance

    𝓢urjectivityExtensionFinExtensionTerm : Surjectivity!.class (Extension Fin) (Extension Term)
    𝓢urjectivityExtensionFinExtensionTerm .⋆ _ _ = 𝓼urjectivityExtensionFinExtensionTerm

    𝓢urjectivityExtensionFinExtensionTerms : ∀ {N} → Surjectivity!.class (Extension Fin) (Extension $ Terms N)
    𝓢urjectivityExtensionFinExtensionTerms .⋆ _ _ = 𝓼urjectivityExtensionFinExtensionTerms
