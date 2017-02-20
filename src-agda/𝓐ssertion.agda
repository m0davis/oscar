
module 𝓐ssertion where

open import OscarPrelude

record 𝓐ssertion (A : Set) : Set
 where
  no-eta-equality

instance 𝓐ssertionList : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (List A)
𝓐ssertionList = record {}
