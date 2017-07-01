
module Oscar.Category.Monoid where

open import Oscar.Level

record Monoid 𝔬 𝔪 𝔮 : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮)) where
