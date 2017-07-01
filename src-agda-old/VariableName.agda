
module VariableName where

open import OscarPrelude

record VariableName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open VariableName public

instance EqVariableName : Eq VariableName
Eq._==_ EqVariableName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)
