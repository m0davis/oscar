
module HasDecidableSatisfaction where

open import OscarPrelude
open import 𝓐ssertion
open import HasSatisfaction
open import Interpretation

record HasDecidableSatisfaction (A : Set) ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)

open HasDecidableSatisfaction ⦃ … ⦄ public

{-# DISPLAY HasDecidableSatisfaction._⊨?_ _ = _⊨?_ #-}
