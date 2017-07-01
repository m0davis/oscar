
module PredicateName where

open import OscarPrelude

record PredicateName : Set
 where
  constructor ⟨_⟩
  field
    name : Nat

open PredicateName public

instance EqPredicateName : Eq PredicateName
Eq._==_ EqPredicateName _ = decEq₁ (cong name) ∘ (_≟_ on name $ _)
