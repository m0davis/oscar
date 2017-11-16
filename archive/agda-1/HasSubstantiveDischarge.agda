{-# OPTIONS --allow-unsolved-metas #-}
module HasSubstantiveDischarge where

open import OscarPrelude

record HasSubstitution (T : Set) (S : Set) : Set where
  field
    _◃_ : S → T → T

open HasSubstitution ⦃ … ⦄ public

record HasPairUnification (T : Set) (S : Set) : Set where
  field
    ⦃ hasSubstitution ⦄ : HasSubstitution T S

  Property : Set₁
  Property = S × S → Set

  Nothing : Property → Set
  Nothing P = ∀ s → P s → ⊥

  IsPairUnifier : (t₁ t₂ : T) → Property
  IsPairUnifier t₁ t₂ s = let s₁ , s₂ = s in s₁ ◃ t₁ ≡ s₂ ◃ t₂

  field
    unify : (t₁ t₂ : T) → Dec ∘ ∃ $ IsPairUnifier t₁ t₂

open HasPairUnification ⦃ … ⦄ public

open import HasNegation

record HasSubstantiveDischarge (A : Set) : Set₁
 where
  field
    _o≽o_ : A → A → Set

  field
    ⦃ hasNegation ⦄ : HasNegation A

  _⋡_ : A → A → Set
  _⋡_ (+) (-) = ¬ + o≽o -

  field
    ≽-reflexive : (x : A) → x o≽o x
    ≽-consistent : (+ - : A) → + o≽o - → + ⋡ ~ -
    ≽-contrapositive : ∀ x y → ~ x o≽o y → x o≽o ~ y

  ≽-contrapositive' : ∀ x y → x o≽o ~ y → ~ x o≽o y
  ≽-contrapositive' = {!!}

open HasSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasSubstantiveDischarge._o≽o_ _ = _o≽o_ #-}

open import Membership

record HasGenericSubstantiveDischarge (A : Set) (B : Set) : Set₁
 where
  field
    _≽_ : A → B → Set

open HasGenericSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasGenericSubstantiveDischarge._≽_ _ = _≽_ #-}

instance HasGenericSubstantiveDischargeReflexive : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → HasGenericSubstantiveDischarge A A
HasGenericSubstantiveDischarge._≽_ HasGenericSubstantiveDischargeReflexive = _o≽o_

instance HasGenericSubstantiveDischargeAList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → HasGenericSubstantiveDischarge A (List A)
HasGenericSubstantiveDischarge._≽_ (HasGenericSubstantiveDischargeAList {A}) (+) -s = ∃ λ (i : A) → i ∈ -s × (+ ≽ i)

instance HasGenericSubstantiveDischargeListA : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → HasGenericSubstantiveDischarge (List A) A
HasGenericSubstantiveDischarge._≽_ (HasGenericSubstantiveDischargeListA {A}) (+s) (-) = ∃ λ (c : A) → c ∈ +s × c ≽ -

instance HasGenericSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → HasGenericSubstantiveDischarge (List A) (List A)
HasGenericSubstantiveDischarge._≽_ (HasGenericSubstantiveDischargeListList {A}) +s -s = ∀ (i : A) → i ∈ -s → +s ≽ i

⋆≽⋆-reflexive : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → (xs : List A) → xs ≽ xs
⋆≽⋆-reflexive _ i i∈ys⋆ = _ , i∈ys⋆ , ≽-reflexive i

◁_ : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → List A → Set
◁_ {A} +s = ∃ λ (s : A) → s ∈ +s × +s ≽ ~ s

⋪_ : ∀ {A} ⦃ _ : HasSubstantiveDischarge A ⦄ → List A → Set
⋪_ = ¬_ ∘ ◁_

record HasDecidableSubstantiveDischarge (A : Set) : Set₁
 where
  field
    ⦃ hasSubstantiveDischarge ⦄ : HasSubstantiveDischarge A
    _≽?_ : (+ - : A) → Dec $ + o≽o -

open HasDecidableSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasDecidableSubstantiveDischarge._≽?_ _ = _≽?_ #-}

_⋆≽?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+s : List A) → (- : A) → Dec (+s ≽ -)
_⋆≽?_ [] - = no λ { (_ , () , _)}
_⋆≽?_ (+ ∷ +s) - with + ≽? -
… | yes +≽- = yes $ _ , zero , +≽-
… | no +⋡- with +s ⋆≽? -
… | yes (+' , +'∈+s , +'≽-) = yes $ _ , suc +'∈+s , +'≽-
… | no +s⋡- = no λ { (_ , zero , +≽-) → +⋡- +≽-
                   ; (+' , suc +'∈+s , +'≽-) → +s⋡- $ _ , +'∈+s , +'≽- }

_≽⋆?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+ : A) → (-s : List A) → Dec (+ ≽ -s)
+ ≽⋆? [] = no (λ { (fst₁ , () , snd₁)})
+ ≽⋆? (- ∷ -s) with + ≽? -
… | yes +≽- = yes (_ , zero , +≽-)
… | no +⋡- with + ≽⋆? -s
… | yes (_ , i∈-s , +≽⋆i) = yes (_ , suc i∈-s , +≽⋆i)
… | no +⋡⋆-s = no (λ { (_ , zero , +≽-) → +⋡- +≽-
                     ; (_ , suc -'∈-s , +≽-') → +⋡⋆-s (_ , -'∈-s , +≽-')})

_⋆≽⋆?_ : ∀ {A} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → (+s : List A) → (-s : List A) → Dec (+s ≽ -s)
_⋆≽⋆?_ +s [] = yes λ _ ()
_⋆≽⋆?_ +s (- ∷ -s) with +s ⋆≽? -
… | no +s⋡- = no λ +s≽-∷-s → +s⋡- $ +s≽-∷-s (-) zero
… | yes +s≽- with +s ⋆≽⋆? -s
… | yes +s≽-s = yes λ { _ zero → +s≽-
                      ; -' (suc -'∈-∷-s) → +s≽-s -' -'∈-∷-s }
… | no +s⋡-s = no λ +s≽-∷-s → +s⋡-s λ +' +'∈-s → +s≽-∷-s +' (suc +'∈-s)

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
