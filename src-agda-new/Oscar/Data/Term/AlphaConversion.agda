
module Oscar.Data.Term.AlphaConversion {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term FunctionName

open import Oscar.Class.AlphaConversion
open import Oscar.Data.Equality
open import Oscar.Data.Fin
open import Oscar.Data.Vec
open import Oscar.Function
open import Oscar.Relation

import Oscar.Data.Term.AlphaConversion.internal FunctionName as ⋆

instance AlphaConversionFinTerm : AlphaConversion Fin Term
AlphaConversion._◂_ AlphaConversionFinTerm = ⋆._◂_
AlphaConversion.◂-identity AlphaConversionFinTerm = ⋆.◂-identity
AlphaConversion.◂-associativity AlphaConversionFinTerm = ⋆.◂-associativity
AlphaConversion.◂-extensionality AlphaConversionFinTerm = ⋆.◂-extensionality

instance AlphaConversionFinTerms : ∀ {N} → AlphaConversion Fin (Terms N)
AlphaConversion._◂_ AlphaConversionFinTerms _ = ⋆._◂s_ _
AlphaConversion.◂-identity AlphaConversionFinTerms = ⋆.◂s-identity
AlphaConversion.◂-associativity AlphaConversionFinTerms _ _ = ⋆.◂s-associativity _ _
AlphaConversion.◂-extensionality AlphaConversionFinTerms f≡̇g = ⋆.◂s-extensionality f≡̇g
