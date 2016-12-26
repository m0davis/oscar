
module Successor where

open import OscarPrelude

record Successor {ℓᴬ} (A : Set ℓᴬ) {ℓᴮ} (B : Set ℓᴮ) : Set (ℓᴬ ⊔ ℓᴮ)
 where
  field
    ⊹ : A → B

open Successor ⦃ … ⦄ public

instance SuccessorNat : Successor Nat Nat
Successor.⊹ SuccessorNat = suc

instance SuccessorLevel : Successor Level Level
Successor.⊹ SuccessorLevel = lsuc
