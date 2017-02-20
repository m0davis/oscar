
module HasSatisfaction where

open import OscarPrelude
open import Interpretation

record HasSatisfaction (A : Set) : Set₁
 where
  field
    _⊨_ : Interpretation → A → Set

  _⊭_ : Interpretation → A → Set
  _⊭_ I = ¬_ ∘ I ⊨_

open HasSatisfaction ⦃ … ⦄ public

{-# DISPLAY HasSatisfaction._⊨_ _ = _⊨_ #-}
{-# DISPLAY HasSatisfaction._⊭_ _ = _⊭_ #-}

instance HasSatisfactionList : {A : Set} ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction $ List A
HasSatisfaction._⊨_ HasSatisfactionList I [] = ⊤
HasSatisfaction._⊨_ HasSatisfactionList I (x ∷ xs) = I ⊨ x × I ⊨ xs

module _ {A} ⦃ _ : HasSatisfaction A ⦄
 where

   ⊨_ : A → Set
   ⊨ x = (I : Interpretation) → I ⊨ x

   ⊭_ : A → Set
   ⊭_ = ¬_ ∘ ⊨_

record HasDecidableValidation (A : Set) ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    ⊨?_ : (x : A) → Dec $ ⊨ x

open HasDecidableValidation ⦃ … ⦄ public

{-# DISPLAY HasDecidableValidation.⊨?_ _ = ⊨?_ #-}

record HasDecidableSatisfaction (A : Set) ⦃ _ : HasSatisfaction A ⦄ : Set₁
 where
  field
    _⊨?_ : (I : Interpretation) → (x : A) → Dec (I ⊨ x)

open HasDecidableSatisfaction ⦃ … ⦄ public

{-# DISPLAY HasDecidableSatisfaction._⊨?_ _ = _⊨?_ #-}
