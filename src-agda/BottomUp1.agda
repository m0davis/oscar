{-# OPTIONS --show-implicit #-}

module BottomUp1 where

record R (_ : Set) : Set where
  no-eta-equality

record S (F : Set → Set)
         ⦃ _ : {A : Set} → R (F A) ⦄
       : Set where

module M0 where
  private
    postulate
      F : Set → Set
      instance Ri : {A : Set} → R (F A)
      instance Si : S F

module M1 (_ : Set) where
  private
    postulate
      F : Set → Set
      instance Ri : {A : Set} → R (F A)
      instance Si-works : S F ⦃ Ri ⦄
      instance Si-fails : S F
      {- No instance of type R (F A) was found in scope. -}
