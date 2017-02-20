
module Vector where

open import OscarPrelude
open import Arity

record Vector (A : Set) (𝑎 : Arity) : Set
 where
  constructor ⟨_⟩
  field
    vector : Vec A (arity 𝑎)

open Vector public

instance EqVector : {A : Set} ⦃ _ : Eq A ⦄ {𝑎 : Arity} → Eq (Vector A 𝑎)
Eq._==_ EqVector _ = decEq₁ (cong vector) ∘ (_≟_ on vector $ _)
