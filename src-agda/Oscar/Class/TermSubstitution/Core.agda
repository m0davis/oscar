
module Oscar.Class.TermSubstitution.Core {𝔣} (FunctionName : Set 𝔣) where

open import Data.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Class.TermSubstitution.Internal

open import Oscar.Class.TermSubstitution.Internal public using (_⊸_)
