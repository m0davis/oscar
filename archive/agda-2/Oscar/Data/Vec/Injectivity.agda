
module Oscar.Data.Vec.Injectivity where

open import Oscar.Data.Equality
open import Oscar.Data.Vec

Vec-head-inj : ∀ {a} {A : Set a} {x₁ x₂ : A} {N} {xs₁ xs₂ : Vec A N} → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂ → x₁ ≡ x₂
Vec-head-inj refl = refl

Vec-tail-inj : ∀ {a} {A : Set a} {x₁ x₂ : A} {N} {xs₁ xs₂ : Vec A N} → x₁ ∷ xs₁ ≡ x₂ ∷ xs₂ → xs₁ ≡ xs₂
Vec-tail-inj refl = refl
