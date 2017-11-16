
module Oscar.Function where

open import Function public using (id; _∘_; _∘′_; flip; _on_; _$_) renaming (const to const_)

infix -1 _∋_
_∋_ : ∀ {a} (A : Set a) → A → A
_ ∋ x = x

open import Prelude.Function public using (it)
