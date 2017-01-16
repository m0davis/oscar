
module Validation where

open import OscarPrelude
open import 𝓐ssertion
open import HasSatisfaction
open import Interpretation

module _ {A} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄
 where

   ⊨_ : A → Set
   ⊨ x = (I : Interpretation) → I ⊨ x

   ⊭_ : A → Set
   ⊭_ = ¬_ ∘ ⊨_

module _ {A} ⦃ _ : HasSatisfaction' A ⦄
 where

   ⊨'_ : A → Set
   ⊨' x = (I : Interpretation) → I ⊨' x

   ⊭'_ : A → Set
   ⊭'_ = ¬_ ∘ ⊨'_
