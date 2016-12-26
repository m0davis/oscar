
module Arity where

open import OscarPrelude

record Arity : Set
 where
  constructor ⟨_⟩
  field
    arity : Nat

open Arity public

instance EqArity : Eq Arity
Eq._==_ EqArity _ = decEq₁ (cong arity) ∘ (_≟_ on arity $ _)
