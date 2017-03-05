
module Oscar.Class.ExtensionalEquality where

open import Oscar.Level

record ExtensionalEquality {a b} (A : Set a) (B : A → Set b) : Set (lsuc (a ⊔ b)) where
  field
    _≐_ : (f g : (x : A) → B x) → Set (a ⊔ b)

open ExtensionalEquality ⦃ … ⦄ public
