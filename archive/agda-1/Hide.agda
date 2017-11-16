module Hide where

record 𝔹ottom : Set₁ where
  field
    ⊥ : Set

open 𝔹ottom ⦃ … ⦄ public

𝔹ottomPrelude : 𝔹ottom
𝔹ottomPrelude = record { ⊥ = P.⊥ } where
  open import Prelude.Empty as P

instance instance𝔹ottom : 𝔹ottom
instance𝔹ottom = 𝔹ottomPrelude
