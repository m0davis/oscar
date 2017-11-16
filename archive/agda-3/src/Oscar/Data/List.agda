
open import Oscar.Prelude

module Oscar.Data.List where

open import Agda.Builtin.List public
  using ()
  renaming ([] to ∅)
  renaming (_∷_ to _,_)
⟨_⟩¶ = Agda.Builtin.List.List

List⟨_⟩ = ⟨_⟩¶
