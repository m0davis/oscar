
module HasSatisfaction where

open import OscarPrelude
open import 𝓐ssertion
open import Interpretation

record HasSatisfaction (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set₁
 where
  field
    _⊨_ : Interpretation → A → Set

  _⊭_ : Interpretation → A → Set
  _⊭_ I = ¬_ ∘ I ⊨_

open HasSatisfaction ⦃ … ⦄ public

{-# DISPLAY HasSatisfaction._⊨_ _ = _⊨_ #-}
{-# DISPLAY HasSatisfaction._⊭_ _ = _⊭_ #-}

record HasSatisfaction' (A : Set) : Set₁
 where
  field
    ⦃ assertion ⦄ : 𝓐ssertion A
    _⊨'_ : Interpretation → A → Set

  _⊭'_ : Interpretation → A → Set
  _⊭'_ I = ¬_ ∘ I ⊨'_

open HasSatisfaction' ⦃ … ⦄ public

{-# DISPLAY HasSatisfaction'._⊨'_ _ = _⊨'_ #-}
{-# DISPLAY HasSatisfaction'._⊭'_ _ = _⊭'_ #-}

instance HasSatisfactionList : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

instance HasSatisfaction'List : {A : Set} ⦃ _ : HasSatisfaction' A ⦄ → HasSatisfaction' $ List A
HasSatisfaction'._⊨'_ HasSatisfaction'List I [] = ⊤
HasSatisfaction'._⊨'_ HasSatisfaction'List I (x ∷ xs) = I ⊨' x × I ⊨' xs
