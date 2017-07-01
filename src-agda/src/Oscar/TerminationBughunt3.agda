
module Oscar.TerminationBughunt3 where

open import Oscar.Prelude
open import Oscar.Data

record 𝓢urjection {𝔬₁} (𝔒₁ : Ø 𝔬₁) {𝔬₂} (𝔒₂ : Ø 𝔬₂) : Ø 𝔬₁ ∙̂ 𝔬₂ where
  field surjection : 𝔒₁ → 𝔒₂
open 𝓢urjection ⦃ … ⦄ public

𝓼urjectivity :
  ∀ {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    -- ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    (s : 𝓢urjection 𝔒₁ 𝔒₂)
    → Ø 𝔯₂ ∙̂ 𝔯₁ ∙̂ 𝔬₁
𝓼urjectivity _∼₁_ _∼₂_ s = let instance _ = s in ∀ {x y} → x ∼₁ y → surjection x ∼₂ surjection y

𝓼urjectivity' :
  ∀ {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔯₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₂)
    → Ø 𝔯₂ ∙̂ 𝔯₁ ∙̂ 𝔬₁
𝓼urjectivity' _∼₁_ _∼₂_ = ∀ {x y} → x ∼₁ y → x ∼₂ y

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  postulate _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

postulate
  𝔓 : Ø₀

open Substitunction 𝔓
open Term 𝔓
open Substitist 𝔓

postulate fmapMaybe : ∀ {𝔬₁ 𝔬₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → Maybe 𝔒₁ → Maybe 𝔒₂
postulate bindMaybe : ∀ {𝔬₁ 𝔬₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → (𝔒₁ → Maybe 𝔒₂) → Maybe 𝔒₂

postulate
  𝓼urjectivitySubstitunctionExtensionTerm' :
    𝓼urjectivity Substitunction (Extension Term) 𝓢urjectionIdentity -- ⦃ 𝓢urjectionIdentity ⦄

  𝓼urjectivitySubstitunctionExtensionTerm'' :
    𝓼urjectivity' Substitunction (Extension Term)
    -- ∀ {x y} → Substitunction x y → Extension Term x y

  someterm : ∀ {m} → Term m

⋆amguTerm! : ∀ {m} (s t : Term m) (acc : ∃ Sub m) -> Maybe (∃ Sub m)
⋆amguTerm! leaf leaf acc = ↑ acc
⋆amguTerm! leaf (function _ _) acc = ∅
⋆amguTerm! leaf (s' fork t') acc = ∅
⋆amguTerm! (s' fork t') leaf acc = ∅
⋆amguTerm! (s' fork t') (function _ _) acc = ∅
⋆amguTerm! (s1 fork s2) (t1 fork t2) acc = bindMaybe {-(⋆amguTerm! s1 t1 acc)-} (⋆amguTerm! s2 t2)
⋆amguTerm! (function fn₁ ts₁) leaf acc = ∅
⋆amguTerm! (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = ∅
⋆amguTerm! (function fn₁ ts₁) (_ fork _) acc = ∅
⋆amguTerm! (i x) (i y) (m , ∅) = ∅
⋆amguTerm! (i x) t     (m , ∅) = ∅
⋆amguTerm! t     (i x) (m , ∅) = ∅
⋆amguTerm! s     t  (n , z / r asub σ) =
  fmapMaybe
  -- (λ σ' → σ' ∃asub r / z)
  (⋆amguTerm!
    (
      𝓼urjectivitySubstitunctionExtensionTerm'
      (r for z) s
    )
    someterm
    (n , σ)
  )
