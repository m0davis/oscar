
module HasDecidableVacuousDischarge where

open import OscarPrelude
open import HasNegation
open import HasSubstantiveDischarge
open import HasVacuousDischarge

record HasDecidableVacuousDischarge (A : Set)
                                    ⦃ _ : HasNegation A ⦄
                                    ⦃ _ : HasSubstantiveDischarge A A ⦄
                                    ⦃ _ : HasVacuousDischarge A ⦄
                                    --⦃ _ : HasDecidableSubstantiveDischarge A A ⦄
                                    --⦃ _ : SubstantiveDischargeIsConsistent A A ⦄
                                    --⦃ _ : SubstantiveDischargeIsReflexive A ⦄
                                    ⦃ _ : Eq A ⦄
                                    : Set₁
 where
  field
    ◁?_ : (x : List A) → Dec $ ◁ x
{-
instance
  ◁? [] = no (λ { (_ , (_ , () , _) , _)})
  ◁? (x ∷ xs) with xs ≽? ~ x
  ◁? (x ∷ xs) | yes (, ~x!∈xs , ~x!≽~x) = yes $ , (((, (here xs , ≽-reflexive x)) , (, (there _ ~x!∈xs , ~x!≽~x))))
  ◁? (x ∷ xs) | no xs⋡~x with ◁? xs
  ◁? (x ∷ xs) | no xs⋡~x | yes (◁pattern c₁∈xs c₁≽s c₂∈xs c₂≽~s) = yes (◁pattern (there _ c₁∈xs) c₁≽s (there _ c₂∈xs) c₂≽~s)
  ◁? (x ∷ xs) | no xs⋡~x | no ⋪xs = no λ
    { (◁pattern (here .xs) x≽s (here .xs) c₂≽~s) → {!xs⋡~x!}
    ; (◁pattern (here .xs) x≽s (there _ c₂∈xs) c₂≽~s) → {!xs⋡~x!}
    ; (◁pattern (there _ c₁∈xs) c₁≽s c₂∈xxs c₂≽~s) → {!xs⋡~x!} }
-}
--{-⋪xs (◁pattern {!!} c₁≽s {!!} c₂≽~s)-}
open HasDecidableVacuousDischarge ⦃ … ⦄

{-# DISPLAY HasDecidableVacuousDischarge.◁?_ _ = ◁?_ #-}
