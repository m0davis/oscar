
open import Oscar.Prelude
open import Oscar.Data.¶
open import Oscar.Data.Fin
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Maybe
open import Oscar.Data.Proposequality
open import Oscar.Data.Vec
open import Oscar.Class.Congruity
open import Oscar.Class.Thickandthin
open import Oscar.Class.Injectivity
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Pure
open import Oscar.Class.Apply
import Oscar.Property.Monad.Maybe
import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality
import Oscar.Class.Surjection.⋆
import Oscar.Class.Congruity.Proposequality
import Oscar.Class.Injectivity.Vec
import Oscar.Class.Surjectivity.ExtensionFinExtensionTerm

module Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  instance

    [𝓣hick]FinTerm : [𝓣hick] Fin Term
    [𝓣hick]FinTerm = ∁

    𝓣hickFinTerm : 𝓣hick Fin Term
    𝓣hickFinTerm .𝓣hick.thick x t = thick x ◃ t

    [𝓣hick]FinTerms : ∀ {N} → [𝓣hick] Fin (Terms N)
    [𝓣hick]FinTerms = ∁

    𝓣hickFinTerms : ∀ {N} → 𝓣hick Fin (Terms N)
    𝓣hickFinTerms .𝓣hick.thick x t = thick x ◃ t

    [𝓣hin]FinTerm : [𝓣hin] Fin Term
    [𝓣hin]FinTerm = ∁

    𝓣hinFinTerm : 𝓣hin Fin Term
    𝓣hinFinTerm .𝓣hin.thin = surjectivity ∘ thin

    [𝓣hin]FinTerms : ∀ {N} → [𝓣hin] Fin (Terms N)
    [𝓣hin]FinTerms = ∁

    𝓣hinFinTerms : ∀ {N} → 𝓣hin Fin (Terms N)
    𝓣hinFinTerms .𝓣hin.thin = surjectivity ∘ thin

    [𝓘njectivity₂,₁]FinTerm : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Term m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerm = ∁

    𝓘njection₂FinTerm : ∀ {m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Term m) → Term (↑ m))
    𝓘njection₂FinTerm {m} .𝓘njection₂.injection₂ = thin

    [𝓘njectivity₂,₁]FinTerms : ∀ {N m} → [𝓘njectivity₂,₁] (𝔱hin Fin (Terms N) m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerms = ∁

    𝓘njection₂FinTerms : ∀ {N m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Terms N m) → Terms N (↑ m))
    𝓘njection₂FinTerms {m} .𝓘njection₂.injection₂ = thin




    𝓘njection₁-TermI : ∀ {n} → 𝓘njection₁ (λ (_ : ¶⟨< n ⟩) → Term n)
    𝓘njection₁-TermI .𝓘njection₁.injection₁ = i

    [𝓘njectivity₁]TermI : ∀ {n} → [𝓘njectivity₁] (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    [𝓘njectivity₁]TermI = ∁

    𝓘njectivity₁TermI : ∀ {n} → 𝓘njectivity₁ (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    𝓘njectivity₁TermI {n} .𝓘njectivity₁.injectivity₁ ∅ = ∅

    𝓘njection₂-TermFork : ∀ {n} → 𝓘njection₂ (λ (_ : Term n) (_ : Term n) → Term n)
    𝓘njection₂-TermFork .𝓘njection₂.injection₂ = _fork_

    [𝓘njection₂,₀,₁]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₁] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₁]-TermFork = ∁

    𝓘njection₂,₀,₁-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₁ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₁-TermFork .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

    [𝓘njection₂,₀,₂]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₂] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₂]-TermFork = ∁

    𝓘njection₂,₀,₂-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₂ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₂-TermFork .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

    𝓘njection₃TermFunction : ∀ {n} → 𝓘njection₃ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n)
    𝓘njection₃TermFunction {n} .𝓘njection₃.injection₃ p N ts = function p ts

    [𝓘njectivity₃,₀,₁]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₁] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₁]TermFunction = ∁

    𝓘njectivity₃,₀,₁TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₁ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₁TermFunction .𝓘njectivity₃,₀,₁.injectivity₃,₀,₁ ∅ = ∅

    [𝓘njectivity₃,₀,₂]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₂] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₂]TermFunction = ∁

    𝓘njectivity₃,₀,₂TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₂ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₂TermFunction .𝓘njectivity₃,₀,₂.injectivity₃,₀,₂ ∅ = ∅

    𝓘njection₂TermFunction : ∀ {N n} → 𝓘njection₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n)
    𝓘njection₂TermFunction {N} {n} .𝓘njection₂.injection₂ p ts = function p ts

    [𝓘njectivity₂,₀,₂]TermFunction : ∀ {N n} → [𝓘njectivity₂,₀,₂] (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₂,₀,₂]TermFunction = ∁

    𝓘njectivity₂,₀,₂TermFunction : ∀ {N n} → 𝓘njectivity₂,₀,₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₂,₀,₂TermFunction .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

  mutual

    instance

      𝓘njectivity₂,₁FinTerm : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Term m) Proposequality Proposequality
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {i _} {i _} eq = congruity i (injectivity₂,₁ x (injectivity₁[ Proposequality ] eq))
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {leaf} _ = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {y₁ fork y₂} {y₃ fork y₄} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₁} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {y₁ fork y₂} {function x₁ x₂} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {i x₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {y₂ fork y₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {function p1 {N1} ts1} {function p2 {N2} ts2} t₁≡t₂
        rewrite injectivity₃,₀,₁[ Proposequality ] {x₂ = p2} t₁≡t₂
        with injectivity₃,₀,₂[ Proposequality ] {y₂ = N2} t₁≡t₂
      … | ∅
        with injectivity₂,₀,₂[ Proposequality ] {y₂ = thin x ts2} t₁≡t₂
      … | ts₁≡ts₂ = congruity (function p2) (injectivity₂,₁ x ts₁≡ts₂)

      𝓘njectivity₂,₁FinTerms : ∀ {N m} → 𝓘njectivity₂,₁ (𝔱hin Fin (Terms N) m) Proposequality Proposequality
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {∅} {∅} x₁ = ∅
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {_ , _} {t₂ , ts₂} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = t₂} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = ts₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅

  instance

    [𝓒heck]FinTermMaybe : [𝓒heck] Fin Term Maybe
    [𝓒heck]FinTermMaybe = ∁

    [𝓒heck]FinTermsMaybe : ∀ {N} → [𝓒heck] Fin (Terms N) Maybe
    [𝓒heck]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heckFinTermMaybe : 𝓒heck Fin Term Maybe
      𝓒heckFinTermMaybe .𝓒heck.check x (i y) = ⦇ i (check x y) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x leaf = ⦇ leaf ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (y₁ fork y₂) = ⦇ _fork_ (check x y₁) (check x y₂) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (function p ts) = ⦇ (function p) (check x ts) ⦈

      𝓒heckFinTermsMaybe : ∀ {N} → 𝓒heck Fin (Terms N) Maybe
      𝓒heckFinTermsMaybe .𝓒heck.check _ ∅ = ⦇ ∅ ⦈
      𝓒heckFinTermsMaybe .𝓒heck.check x (t , ts) = ⦇ check x t , check x ts ⦈

  instance

    [𝓣hick/thin=1]FinTermProposequality : [𝓣hick/thin=1] Fin Term Proposequality
    [𝓣hick/thin=1]FinTermProposequality = ∁

    [𝓣hick/thin=1]FinTermsProposequality : ∀ {N} → [𝓣hick/thin=1] Fin (Terms N) Proposequality
    [𝓣hick/thin=1]FinTermsProposequality = ∁

  mutual

    instance

      𝓣hick/thin=1FinTermProposequality : 𝓣hick/thin=1 Fin Term Proposequality
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (i y) rewrite thick/thin=1 {_≈_ = Proposequality} x y = ∅ -- congruity i $ thick/thin=1 x y
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x leaf = ∅
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (y₁ fork y₂) = congruity₂ _fork_ (thick/thin=1 x y₁) (thick/thin=1 x y₂)
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (function p ts) = congruity (function p) (thick/thin=1 x ts)

      𝓣hick/thin=1FinTermsProposequality : ∀ {N} → 𝓣hick/thin=1 Fin (Terms N) Proposequality
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x (t , ts) = congruity₂ _,_ (thick/thin=1 x t) (thick/thin=1 x ts)

  instance

    [𝓒heck/thin=1]FinTermMaybe : [𝓒heck/thin=1] Fin Term Maybe Proposequality
    [𝓒heck/thin=1]FinTermMaybe = ∁

    [𝓒heck/thin=1]FinTermsMaybe : ∀ {N} → [𝓒heck/thin=1] Fin (Terms N) Maybe Proposequality
    [𝓒heck/thin=1]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heck/thin=1FinTermMaybe : 𝓒heck/thin=1 Fin Term Maybe Proposequality
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (i y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x leaf = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (y₁ fork y₂)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₁
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₂
        = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (function p ys) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys = ∅

      𝓒heck/thin=1FinTermsMaybe : ∀ {N} → 𝓒heck/thin=1 Fin (Terms N) Maybe Proposequality
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x ∅ = ∅
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x (y , ys)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys
        = ∅

  instance

    IsThickandthinFinTerm : IsThickandthin Fin Term Proposequality Maybe Proposequality
    IsThickandthinFinTerm = ∁

    IsThickandthinFinTerms : ∀ {N} → IsThickandthin Fin (Terms N) Proposequality Maybe Proposequality
    IsThickandthinFinTerms = ∁

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  ThickandthinFinTerm : Thickandthin _ _ _ _ _ _
  ThickandthinFinTerm = ∁ Fin Term Proposequality Maybe Proposequality

  ThickandthinFinTerms : ∀ N → Thickandthin _ _ _ _ _ _
  ThickandthinFinTerms N = ∁ Fin (Terms N) Proposequality Maybe Proposequality
