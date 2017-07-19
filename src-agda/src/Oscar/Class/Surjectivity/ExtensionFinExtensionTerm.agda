
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Class.Surjection

module Oscar.Class.Surjectivity.ExtensionFinExtensionTerm where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Term 𝔓

  private

    mutual

      𝓼urjectivityExtensionFinExtensionTerm : 𝓼urjectivity (Extension Fin) (Extension Term)
      𝓼urjectivityExtensionFinExtensionTerm x (i y) = i (x y)
      𝓼urjectivityExtensionFinExtensionTerm x leaf = leaf
      𝓼urjectivityExtensionFinExtensionTerm x (l fork r) = 𝓼urjectivityExtensionFinExtensionTerm x l fork 𝓼urjectivityExtensionFinExtensionTerm x r
      𝓼urjectivityExtensionFinExtensionTerm x (function f ts) = function f $ 𝓼urjectivityExtensionFinExtensionTerms x ts

      𝓼urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓼urjectivity (Extension Fin) (Extension $ Terms N)
      𝓼urjectivityExtensionFinExtensionTerms x ∅ = ∅
      𝓼urjectivityExtensionFinExtensionTerms x (t , ts) = 𝓼urjectivityExtensionFinExtensionTerm x t , 𝓼urjectivityExtensionFinExtensionTerms x ts

  instance

    [𝓢urjectivity]ExtensionFinExtensionTerm : [𝓢urjectivity] (Extension Fin) (Extension Term)
    [𝓢urjectivity]ExtensionFinExtensionTerm = ∁

    𝓢urjectivityExtensionFinExtensionTerm : 𝓢urjectivity (Extension Fin) (Extension Term)
    𝓢urjectivityExtensionFinExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerm

    [𝓢urjectivity]ExtensionFinExtensionTerms : ∀ {N} → [𝓢urjectivity] (Extension Fin) (Extension $ Terms N)
    [𝓢urjectivity]ExtensionFinExtensionTerms = ∁

    𝓢urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓢urjectivity (Extension Fin) (Extension $ Terms N)
    𝓢urjectivityExtensionFinExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerms
