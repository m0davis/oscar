
module FunctionName where

open import OscarPrelude

record FunctionName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open FunctionName public

instance EqFunctionName : Eq FunctionName
Eq._==_ EqFunctionName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)
