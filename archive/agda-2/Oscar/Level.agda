
module Oscar.Level where

open import Agda.Primitive public
  using ()
  renaming (Level to Ł̂; lzero to Ø̂; lsuc to ↑̂_; _⊔_ to _+̂_)

open import Agda.Primitive public
  using ()
  renaming (Level to Ł̂; lzero to lzero; lsuc to lsuc; _⊔_ to _⊔_)

𝑶 : ∀ a → Set (lsuc a)
𝑶 a = Set a

open import Agda.Primitive public
  using ()
  renaming ( Level to Ł
           ; lzero to ∅̂
           ; lsuc to ↑̂_
           ; _⊔_ to _∙̂_ )

infix 0 Ø_
Ø_ : ∀ 𝔬 → Set (↑̂ 𝔬)
Ø_ 𝔬 = Set 𝔬

Ø₀ = Ø ∅̂
