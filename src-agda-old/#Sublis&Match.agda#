module Sublis&Match where
  open import Prelude

  record Container {a : Level} (Carrier : Set a) {b : Level} (Element : Set b) : Set (lsuc (a ⊔ b)) where
    field
      _∈_ : Element → Carrier → Set (a ⊔ b)
      _∈?_ : (e : Element) (c : Carrier) → Dec (e ∈ c)
