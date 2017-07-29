
open import Oscar.Prelude
open import Oscar.Data.¶

module Oscar.Data.Vec where

data ⟨_⟩¶⟨≤_⟩ {𝔭} (𝔓 : ¶ → Ø 𝔭) : ¶ → Ø 𝔭 where
  ∅ : ⟨ 𝔓 ⟩¶⟨≤ ∅ ⟩
  _,_ : ∀ ..{n} → 𝔓 n → ⟨ 𝔓 ⟩¶⟨≤ n ⟩ → ⟨ 𝔓 ⟩¶⟨≤ ↑ n ⟩

Vec⟨_⟩ = ⟨_⟩¶⟨≤_⟩
