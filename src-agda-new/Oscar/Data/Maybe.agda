
module Oscar.Data.Maybe where

open import Data.Maybe public using (Maybe; nothing; just)

-- open import Oscar.Data.Maybe.Core public

-- --open import Data.Maybe public using (maybe)

-- -- open import Relation.Binary.PropositionalEquality
-- -- open import Data.Empty

-- -- unMaybe : ∀ {A : Set} {x y : A} {B : Set} {m : Maybe B} → maybe (λ _ → x) y m ≡ y → x ≢ y → m ≡ nothing
-- -- unMaybe {m = just x₁} x₂ x₃ = ⊥-elim (x₃ x₂)
-- -- unMaybe {m = nothing} x₁ x₂ = refl

-- -- unMaybe' : ∀ {A : Set} {y : A} {B : Set} {x : B → A} {m : Maybe B} → maybe (λ b → x b) y m ≡ y → (∀ b → x b ≢ y) → m ≡ nothing
-- -- unMaybe' {m = just x₁} x₂ x₃ = ⊥-elim (x₃ x₁ x₂)
-- -- unMaybe' {m = nothing} x₁ x₂ = refl

-- -- just≢nothing : ∀ {A B : Set} → (x : B → A) → ∀ b → Maybe.just (x b) ≢ nothing
-- -- just≢nothing x b ()

-- -- unMaybeJust' : ∀ {A B : Set} {P : B → A} {m : Maybe B} {n : A} {x : B} → maybe (λ b → P b) n m ≡ P x → (∀ b → P b ≢ n) → (∀ {y y'} → P y ≡ P y' → y ≡ y') → m ≡ just x
-- -- unMaybeJust' {m = just x} x₂ x₃ inj rewrite inj x₂ = refl
-- -- unMaybeJust' {m = nothing} x₁ x₂ _ = ⊥-elim (x₂ _ (sym x₁))
