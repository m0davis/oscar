
module Oscar.Builtin.Level where

open import Agda.Primitive public
  using ()
  renaming (Level to Ł̂; lzero to Ø̂; lsuc to ↑̂_; _⊔_ to _+̂_)

infix 0 Ø_
Ø_ : ∀ 𝔬 → Set (↑̂ 𝔬)
Ø_ 𝔬 = Set 𝔬
