
open import Oscar.Prelude
open import Oscar.Data

module Oscar.Class.IsDecidable where

record IsDecidable {𝔬} (𝔒 : Ø 𝔬) : Ø 𝔬 where
  infix 4 _≟_
  field
    _≟_ : (x y : 𝔒) → Decidable (x ≡ y)

open IsDecidable ⦃ … ⦄ public
