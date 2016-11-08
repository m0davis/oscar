
module Match-InstanceSearchBug where

module Try1 where

  open import Agda.Builtin.Equality

  record Membership (E G : Set) : Set₁ where
    field _∈_ : E → G → Set

  open Membership ⦃ ... ⦄

  record Valueable (A V : Set) : Set where
    field value : A → V

  open Valueable ⦃ ... ⦄

  record Map (K V M : Set) : Set₁ where
    field
      _∈'_ : K → M → Set
      value' : {k : K} {m : M} → (s : Set) → ⦃ _ : s ≡ V ⦄ → (k∈m : k ∈' m) → V

  open Map ⦃ ... ⦄

  module _
    (K V M : Set)
    ⦃ _ : Map K V M ⦄
    where
    test : (k : K) (m : M) (k∈m : k ∈' m) →
           value' V {{refl}} k∈m ≡ value' V {{refl}} k∈m
    test = {!!}

--   module _
--     (E G V : Set)
--     ⦃ E∈G : Membership E G ⦄
--     ⦃ e∈g→v : {e : E} {g : G} → Valueable (e ∈ g) V ⦄
--     where

--     works : (e : E) (g : G) (e∈g : e ∈ g) →
--           _≡_ {A = V}
--               (value ⦃ e∈g→v ⦄ e∈g)
--               (value ⦃ e∈g→v ⦄ e∈g)
--     works e g e∈g = refl
-- {-
--     fails : (e : E) (g : G) (e∈g : e ∈ g) →
--           _≡_ {A = _}
--               (value ⦃ {!!} ⦄ e∈g)
--               (value ⦃ _ ⦄ e∈g)
--     fails e g e∈g = refl
-- -}
