
module Oscar.Data.Term.ṀonoidFin {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Class.Ṁonoid
open import Oscar.Data.Fin
open import Oscar.Data.Term FunctionName
import Oscar.Data.Term.internal.ṀonoidFin&ṠubstitutionFin FunctionName as ⋆

instance ṀonoidFinTerm : Ṁonoid Fin Term
Ṁonoid.ε̇ ṀonoidFinTerm = ⋆.ε̇
Ṁonoid._◇̇_ ṀonoidFinTerm = ⋆._◇̇_
Ṁonoid.◇̇-left-identity ṀonoidFinTerm = ⋆.◇̇-left-identity
Ṁonoid.◇̇-right-identity ṀonoidFinTerm = ⋆.◇̇-right-identity
Ṁonoid.◇̇-associativity ṀonoidFinTerm = ⋆.◇̇-associativity
