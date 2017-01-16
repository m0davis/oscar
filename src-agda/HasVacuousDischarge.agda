
module HasVacuousDischarge where

open import OscarPrelude
open import HasNegation
open import HasSubstantiveDischarge

record HasVacuousDischarge (A : Set) ⦃ _ : HasNegation A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
 where

  ◁_ : List A → Set
  ◁ +s = ∃ λ (s : A) → (+s ≽ s) × (+s ≽ ~ s)

  ⋪_ : List A → Set
  ⋪_ = ¬_ ∘ ◁_

open HasVacuousDischarge ⦃ … ⦄ public

{-# DISPLAY HasVacuousDischarge.◁_ _ = ◁_ #-}
{-# DISPLAY HasVacuousDischarge.⋪_ _ = ⋪_ #-}

record HasVacuousDischarge' (A : Set) : Set₁
 where
  field
    ⦃ hasNegation ⦄ : HasNegation A
    ⦃ hasSubstantiveDischarge ⦄ : HasSubstantiveDischarge A A

  ◁'_ : List A → Set
  ◁' +s = ∃ λ (s : A) → (+s ≽ s) × (+s ≽ ~ s)

  ⋪'_ : List A → Set
  ⋪'_ = ¬_ ∘ ◁'_

open HasVacuousDischarge' ⦃ … ⦄ public

{-# DISPLAY HasVacuousDischarge'.◁'_ _ = ◁'_ #-}
{-# DISPLAY HasVacuousDischarge'.⋪'_ _ = ⋪'_ #-}
