
module 𝓢equent where

open import OscarPrelude
open import 𝓐ssertion

infix 15 _⊢_
record 𝓢equent (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set
 where
  constructor _⊢_
  field
    antecedents : List A
    consequents : List A

open 𝓢equent ⦃ … ⦄

instance Eq𝓢equent : {A : Set} ⦃ _ : Eq A ⦄ ⦃ _ : 𝓐ssertion A ⦄ → Eq (𝓢equent A)
Eq._==_ Eq𝓢equent (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

instance 𝓐ssertion𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝓢equent A)
𝓐ssertion𝓢equent = record {}
