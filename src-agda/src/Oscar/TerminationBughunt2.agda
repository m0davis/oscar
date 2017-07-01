module Oscar.TerminationBughunt2 where

open import Oscar.Prelude
open import Oscar.Class using (𝓢urjection; 𝓼urjectivity)
open import Oscar.Data

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
  -- open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

  postulate _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

  -- _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n
  -- (t for x) y = maybe′ i t (check {C = Maybe} x y)

postulate
  𝔓 : Ø₀

open Substitunction 𝔓
open Term 𝔓
open Substitist 𝔓
-- open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

postulate fmapMaybe : ∀ {𝔬₁ 𝔬₂} → -- 𝓯map Maybe 𝔬₁ 𝔬₂
            ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} (f : 𝔒₁ → 𝔒₂) → Maybe 𝔒₁ → Maybe 𝔒₂
-- fmapMaybe f ∅ = ∅
-- fmapMaybe f (↑ x) = ↑ f x

postulate bindMaybe : ∀ {𝔬₁ 𝔬₂} → -- 𝓫ind Maybe 𝔬₁ 𝔬₂
            ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → Maybe 𝔒₁ → (𝔒₁ → Maybe 𝔒₂) → Maybe 𝔒₂
-- bindMaybe ∅ _ = ∅
-- bindMaybe (↑ x) f = f x

postulate _∃asub_/_ : ∀ {m} (a : ∃ Sub m) (t' : Term m) (x : Fin (↑ m)) → ∃ Sub (↑ m)
-- (n , σ) ∃asub t' / x = n , x / t' asub σ

postulate
  𝓼urjectivitySubstitunctionExtensionTerm' :
    -- ∀ {x y} → Substitunction x y → Extension Term x y -- surjection x ∼₂ surjection y
    𝓼urjectivity Substitunction (Extension Term)

  𝓼urjectivitySubstitunctionExtensionTerm'' :
    ∀ {x y} → Substitunction x y → Extension Term x y -- surjection x ∼₂ surjection y

  someterm : ∀ {m} → Term m

⋆amguTerm! : ∀ {m} (s t : Term m) (acc : ∃ Sub m) -> Maybe (∃ Sub m)
⋆amguTerm! leaf leaf acc = ↑ acc
⋆amguTerm! leaf (function _ _) acc = ∅
⋆amguTerm! leaf (s' fork t') acc = ∅
⋆amguTerm! (s' fork t') leaf acc = ∅
⋆amguTerm! (s' fork t') (function _ _) acc = ∅
⋆amguTerm! (s1 fork s2) (t1 fork t2) acc = bindMaybe (⋆amguTerm! s1 t1 acc) (⋆amguTerm! s2 t2)
⋆amguTerm! (function fn₁ ts₁) leaf acc = ∅
⋆amguTerm! (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = ∅
⋆amguTerm! (function fn₁ ts₁) (_ fork _) acc = ∅
⋆amguTerm! (i x) (i y) (m , ∅) = ∅
⋆amguTerm! (i x) t     (m , ∅) = ∅
⋆amguTerm! t     (i x) (m , ∅) = ∅
⋆amguTerm! s     t  (n , z / r asub σ) =
  fmapMaybe
  (λ σ' → σ' ∃asub r / z)
  (⋆amguTerm!
    (
      -- § ⦃ 𝓢urjectionIdentity ⦄ ⦃ r = 𝓢urjectivitySubstitunctionExtensionTerm ⦄
      𝓼urjectivitySubstitunctionExtensionTerm'
      (r for z) s
    )
    someterm
    {-(
      -- § ⦃ 𝓢urjectionIdentity ⦄ ⦃ r = 𝓢urjectivitySubstitunctionExtensionTerm ⦄
      𝓼urjectivitySubstitunctionExtensionTerm'
      (r for z) t
    )-}
    (n , σ)
  )
