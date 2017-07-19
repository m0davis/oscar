
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality

module Oscar.Class.Injectivity.Vec where

instance

  𝓘njection₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njection₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N))
  𝓘njection₂Vec .𝓘njection₂.injection₂ = _,_

  [𝓘njectivity₂,₀,₁]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₁] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
  [𝓘njectivity₂,₀,₁]Vec = ∁

  𝓘njectivity₂,₀,₁Vec :   ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₁   (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
  𝓘njectivity₂,₀,₁Vec .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

  [𝓘njectivity₂,₀,₂]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₂] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
  [𝓘njectivity₂,₀,₂]Vec = ∁

  𝓘njectivity₂,₀,₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
  𝓘njectivity₂,₀,₂Vec .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅
