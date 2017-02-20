
module HasDecidableValidation where

open import OscarPrelude
open import 𝓐ssertion
open import HasSatisfaction
open import Validation

record HasDecidableValidation (A : Set) ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    ⊨?_ : (x : A) → Dec $ ⊨ x

open HasDecidableValidation ⦃ … ⦄ public
