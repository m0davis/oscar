
module TruthValue where

open import OscarPrelude

record TruthValue : Set
 where
  constructor ⟨_⟩
  field
    truthValue : Bool

open TruthValue public
