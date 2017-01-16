
module Foundation.Level0 where

record IsBottom (⊥ : Set₀) : Set₁ where
  field
    ⊥-elim : ⊥ → {A : Set₀} → A

open IsBottom ⦃ … ⦄ public
