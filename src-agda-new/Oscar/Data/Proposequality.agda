
module Oscar.Data.Proposequality where

open import Agda.Builtin.Equality public using (_≡_) renaming (refl to ∅) public
open import Relation.Binary.PropositionalEquality public using (_≢_) public

open import Oscar.Category.Setoid

open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Oscar.Level
open import Oscar.Relation

instance

  IsSetoidProposequality : ∀ {a} {A : Set a} → IsSetoid (_≡_ {A = A})
  IsSetoid.reflexivity IsSetoidProposequality _ = ∅
  IsSetoid.symmetry IsSetoidProposequality = sym
  IsSetoid.transitivity IsSetoidProposequality = λ ‵ → trans ‵

module _ {a} (A : Set a) where

  setoid : Setoid a a
  setoid = ↑ _≡_ {A = A}

{-
  private

    infixl 7 _∙_
    _∙_ : Transitive (_≡_ {A = A})
    _∙_ = (λ y≡z x≡y → transitivity x≡y y≡z)
-}

  open import Oscar.Category.Morphism
  open import Oscar.Function

  module _ {b} (B : A → A → Set b) where

{-
    private

      infix 4 _≞_
      _≞_ = λ {x} {y} → _≡_ {A = B x y}
-}
    morphism : Morphism a b b
    morphism = -- ↑ λ {x} {y} → _≞_ {x} {y} -- _≡_ {A = B x y}
               ↑ λ {x} {y} → _≡_ {A = B x y}

    open Morphism morphism

    open import Oscar.Category.Semigroupoid

    module _ (_∙_ : Transitive _↦_) (associativity : Associative _∙_ _≞_) where

      instance

        IsSemigroupoidProposequality : IsSemigroupoid morphism _∙_
        IsSemigroupoid.extensionality IsSemigroupoidProposequality ∅ ∅ = ∅
        IsSemigroupoid.associativity IsSemigroupoidProposequality = associativity

-- instance

--   IsSemigroupoidProposequality : ∀ {a} {A : Set a} {b} {B : A → A → Set b}
--     → IsSemigroupoid (morphism B) {!!} -- (transitivity ⦃ setoid A ⦄)
--   IsSemigroupoidProposequality = {!!}

--   IsSemigroupoidProposequality' : ∀ {a} {A : Set a}
--     → IsSemigroupoid (morphism (_≡_ {A = A})) (λ y≡z x≡y → transitivity x≡y y≡z) -- (transitivity ⦃ setoid A ⦄)
--   IsSemigroupoid.extensionality IsSemigroupoidProposequality' = {!!} -- ∅ ∅ = ∅
--   IsSemigroupoid.associativity IsSemigroupoidProposequality' ∅ _ _ = ∅

-- -- semigroupoid : Semigroupoid



-- -- setoid : ∀ {a} (A : Set a) → Setoid a a
-- -- setoid A = ↑ _≡_ {A = A}

-- -- open import Oscar.Category.Morphism
-- -- open import Oscar.Function

-- -- morphism : ∀ {a} {A : Set a} {b} (B : A → A → Set b) → Morphism a b b
-- -- morphism B = ↑ λ {x} {y} → _≡_ {A = B x y}

-- -- open import Oscar.Category.Semigroupoid

-- -- infixl 7 _∙_
-- -- _∙_ : ∀ {y z} → y ↦ z → ∀ {x} → x ↦ y → x ↦ z

-- -- instance

-- --   IsSemigroupoidProposequality : ∀ {a} {A : Set a} {b} {B : A → A → Set b}
-- --     → IsSemigroupoid (morphism B) {!!} -- (transitivity ⦃ setoid A ⦄)
-- --   IsSemigroupoidProposequality = {!!}

-- --   IsSemigroupoidProposequality' : ∀ {a} {A : Set a}
-- --     → IsSemigroupoid (morphism (_≡_ {A = A})) (λ y≡z x≡y → transitivity x≡y y≡z) -- (transitivity ⦃ setoid A ⦄)
-- --   IsSemigroupoid.extensionality IsSemigroupoidProposequality' = {!!} -- ∅ ∅ = ∅
-- --   IsSemigroupoid.associativity IsSemigroupoidProposequality' ∅ _ _ = ∅

-- -- -- semigroupoid : Semigroupoid
