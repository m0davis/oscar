
module Oscar.Property where

open import Oscar.Builtin.Numbatural
open import Oscar.Builtin.Objectevel

𝑴 : ℕ → ∀ {𝔬} → Ø 𝔬 → ∀ 𝔪 → Ø 𝔬 ∙̂ ↑̂ 𝔪
𝑴 ∅ 𝔒 𝔪 = 𝔒 → Ø 𝔪
𝑴 (↑ n) 𝔒 𝔪 = 𝔒 → 𝑴 n 𝔒 𝔪

𝑴² : ∀ (m : ℕ) n {𝔬} {𝔒 : Ø 𝔬} {𝔪} → 𝑴 n 𝔒 𝔪 → ∀ 𝔮 → Ø 𝔬 ∙̂ 𝔪 ∙̂ ↑̂ 𝔮
𝑴² m ∅ 𝔒 𝔮 = ∀ {o} → 𝑴 m (𝔒 o) 𝔮
𝑴² m (↑ n) 𝔒 𝔮 = ∀ {o} → 𝑴² m n (𝔒 o) 𝔮
