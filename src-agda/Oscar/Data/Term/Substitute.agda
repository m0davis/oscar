
module Oscar.Data.Term.Substitute {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Class.Substitution
open import Oscar.Class.Substitute
open import Oscar.Data.Fin
open import Oscar.Data.Term FunctionName
open import Oscar.Data.Term.Substitution FunctionName
import Oscar.Data.Term.internal.SubstituteAndSubstitution FunctionName as ⋆
open import Oscar.Function

instance SubstituteFinTerm : Substitute Fin Term Term
Substitute.substitution SubstituteFinTerm = SubstitutionFinTerm
Substitute._◃_ SubstituteFinTerm = ⋆._◃_
Substitute.◃-identity SubstituteFinTerm = ⋆.◃-identity
Substitute.◃-associativity SubstituteFinTerm = ⋆.◃-associativity
Substitute.◃-extensionality SubstituteFinTerm = ⋆.◃-extensionality

{-# DISPLAY ⋆._◃_ = Substitute._◃_ SubstituteFinTerm #-}

instance SubstituteFinTerms : ∀ {N} → Substitute Fin Term (Terms N)
Substitute.substitution SubstituteFinTerms = SubstitutionFinTerm
Substitute._◃_ SubstituteFinTerms f = ⋆._◃s_ f
Substitute.◃-identity SubstituteFinTerms = ⋆.◃s-identity
Substitute.◃-associativity SubstituteFinTerms f g = ⋆.◃s-associativity f g
Substitute.◃-extensionality SubstituteFinTerms f≡̇g = ⋆.◃s-extensionality f≡̇g
