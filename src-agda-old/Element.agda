
module Element where

open import OscarPrelude

record Element : Set
 where
  constructor ⟨_⟩
  field
    element : Nat

open Element public

instance EqElement : Eq Element
Eq._==_ EqElement ⟨ ε₁ ⟩ ⟨ ε₂ ⟩ with ε₁ ≟ ε₂
Eq._==_ EqElement ⟨ _ ⟩  ⟨ _ ⟩ | yes refl = yes refl
Eq._==_ EqElement ⟨ _ ⟩  ⟨ _ ⟩ | no ε₁≢ε₂ = no λ {refl → ε₁≢ε₂ refl}
