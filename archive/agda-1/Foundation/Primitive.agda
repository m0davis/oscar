
module Foundation.Primitive where

open import Agda.Primitive

infix -65536 ℞_
℞_ : ∀ ℓ → Set _
℞_ ℓ = Set ℓ

⟰ : Level → Level
⟰ = lsuc

infix -65536 ℞₁_
℞₁_ : ∀ ℓ → Set _
℞₁_ ℓ = ℞ ⟰ ℓ

𝟘 : Level
𝟘 = lzero

open import Agda.Primitive using (_⊔_) public
