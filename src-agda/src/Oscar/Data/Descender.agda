
open import Oscar.Prelude
open import Oscar.Data.¶

module Oscar.Data.Descender where

-- m ≤ n, counting down from n-1 to m
data Descender⟨_⟩ {a} (A : ¶ → Ø a) (m : ¶) : ¶ → Ø a where
  ∅ : Descender⟨ A ⟩ m m
  _,_ : ∀ {n} → A n → Descender⟨ A ⟩ m n → Descender⟨ A ⟩ m (↑ n)

Vec'⟨_⟩ = λ {a} (A : Ø a) N → Descender⟨ (λ _ → A) ⟩ 0 N
⟨_⟩¶⟨_≤_↓⟩ = Descender⟨_⟩
AList⟨_⟩ = ⟨_⟩¶⟨_≤_↓⟩
