
module HasDecidableSubstantiveDischarge where

open import OscarPrelude
open import HasSubstantiveDischarge

record HasDecidableSubstantiveDischarge (A : Set) : Set₁
 where
  field
    ⦃ hasSubstantiveDischarge ⦄ : HasSubstantiveDischarge A
    _≽?_ : (+ - : A) → Dec $ + ≽ -

open HasDecidableSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasDecidableSubstantiveDischarge._≽?_ _ = _≽?_ #-}

open import Membership

_⋆≽?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+s : List A) → (- : A) → Dec (+s ⋆≽ -)
_⋆≽?_ [] - = no λ { (_ , () , _)}
_⋆≽?_ (+ ∷ +s) - with + ≽? -
… | yes +≽- = yes $ _ , zero , +≽-
… | no +⋡- with +s ⋆≽? -
… | yes (+' , +'∈+s , +'≽-) = yes $ _ , suc +'∈+s , +'≽-
… | no +s⋡- = no λ { (_ , zero , +≽-) → +⋡- +≽-
                   ; (+' , suc +'∈+s , +'≽-) → +s⋡- $ _ , +'∈+s , +'≽- }

_≽⋆?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+ : A) → (-s : List A) → Dec (+ ≽⋆ -s)
+ ≽⋆? [] = no (λ { (fst₁ , () , snd₁)})
+ ≽⋆? (- ∷ -s) with + ≽? -
… | yes +≽- = yes (_ , zero , +≽-)
… | no +⋡- with + ≽⋆? -s
… | yes (_ , i∈-s , +≽⋆i) = yes (_ , suc i∈-s , +≽⋆i)
… | no +⋡⋆-s = no (λ { (_ , zero , +≽-) → +⋡- +≽-
                     ; (_ , suc -'∈-s , +≽-') → +⋡⋆-s (_ , -'∈-s , +≽-')})

_⋆≽⋆?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+s : List A) → (-s : List A) → Dec (+s ⋆≽⋆ -s)
_⋆≽⋆?_ +s [] = yes λ _ ()
_⋆≽⋆?_ +s (- ∷ -s) with +s ⋆≽? -
… | no +s⋡- = no λ +s≽-∷-s → +s⋡- $ +s≽-∷-s (-) zero
… | yes +s≽- with +s ⋆≽⋆? -s
… | yes +s≽-s = yes λ { _ zero → +s≽-
                      ; -' (suc -'∈-∷-s) → +s≽-s -' -'∈-∷-s }
… | no +s⋡-s = no λ +s≽-∷-s → +s⋡-s λ +' +'∈-s → +s≽-∷-s +' (suc +'∈-s)

open import HasNegation

◁?_ : ∀ {+} ⦃ _ : HasDecidableSubstantiveDischarge (+) ⦄
            → (+s : List +) → Dec $ ◁ +s
◁? [] = no λ {(_ , () , _)}
◁?_ (+ ∷ +s) with +s ⋆≽? ~ +
… | yes (_ , +'∈+s , +'≽~+) = yes $ _ , zero , _ , suc +'∈+s , +'≽~+
… | no +s⋆⋡~+ with ~ + ≽⋆? +s
… | yes (_ , c∈+s , ~+≽c) = yes (_ , suc c∈+s , _ , zero , ≽-contrapositive (+) _ ~+≽c)
… | no ~+⋡⋆+s with ◁? +s
… | yes (s , s∈+s , c , c∈+s , c≽~s) = yes $ _ , suc s∈+s , _ , suc c∈+s , c≽~s
… | no ⋪+s = no
  λ { (_ , zero , _ , zero , c≽~s) → ≽-consistent (+) (+) (≽-reflexive +) c≽~s
  ; (_ , zero , c , suc c∈+s , c≽~s) → +s⋆⋡~+ (_ , c∈+s , c≽~s)
  ; (s , suc s∈+s , .+ , zero , +≽~s) → ~+⋡⋆+s (_ , s∈+s , ≽-contrapositive' (+) s +≽~s)
  ; (s , suc s∈+s , c , suc c∈+s , c≽~s) → ⋪+s (_ , s∈+s , _ , c∈+s , c≽~s) }
