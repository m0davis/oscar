
module Unification where

open import OscarPrelude
open import Delay
open import VariableName
open import FunctionName
open import Arity
open import Vector
open import Term

mutual
  substituteTerm⇑ : VariableName → Term → ∀ {i} → Term → Delay i Term
  substituteTerm⇑ 𝑥ₛ τₛ τ@(variable 𝑥)  = now $ ifYes 𝑥ₛ ≟ 𝑥 then τₛ else τ
  substituteTerm⇑ 𝑥ₛ τₛ (function 𝑓 τs) =
    substituteTerms⇑ 𝑥ₛ τₛ τs >>= λ τsₛ →
    now $ function 𝑓 τsₛ

  substituteTerms⇑ : VariableName → Term → ∀ {i} → Terms → Delay i Terms
  substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ [] ⟩ ⟩ = now ⟨ ⟨ [] ⟩ ⟩
  substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ τ ∷ τs ⟩ ⟩ =
    let τs = substituteTerms⇑ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩
        τ = substituteTerm⇑ 𝑥ₛ τₛ τ in
    τs >>= λ { ⟨ ⟨ τs ⟩ ⟩ →
    τ >>= λ { τ →
    now $ ⟨ ⟨ τ ∷ τs ⟩ ⟩ } }

substituteTerms⇓ : (𝑥ₛ : VariableName) → (τₛ : Term) → (τs : Terms) → substituteTerms⇑ 𝑥ₛ τₛ τs ⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ [] ⟩ ⟩ = _ , now⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ (variable 𝑥) ∷ τs ⟩ ⟩ = _ , substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ now⇓
substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ (function 𝑓 τs₁) ∷ τs ⟩ ⟩ = _ , substituteTerms⇓ 𝑥ₛ τₛ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ ((substituteTerms⇓ 𝑥ₛ τₛ τs₁ ⇓>>=⇓ now⇓) >>=⇓ now⇓)

substituteTerm⇓ : (𝑥ₛ : VariableName) → (τₛ : Term) → (τ : Term) → substituteTerm⇑ 𝑥ₛ τₛ τ ⇓
substituteTerm⇓ 𝑥ₛ τₛ (variable 𝑥) = _ , now⇓
substituteTerm⇓ 𝑥ₛ τₛ (function 𝑓 τs) = _ , substituteTerms⇓ 𝑥ₛ τₛ τs ⇓>>=⇓ now⇓

substitute : VariableName → Term → Term → Term
substitute 𝑥ₛ τₛ τ = fst $ substituteTerm⇓ 𝑥ₛ τₛ τ

data AListOfSubstitutions : Set
 where
  [] : AListOfSubstitutions
  _∷_ : VariableName × Term → AListOfSubstitutions → AListOfSubstitutions

substituteA : AListOfSubstitutions → Term → Term
substituteA [] τ = τ
substituteA ((𝑥ₛ , τₛ) ∷ as) τ = substituteA as (substitute 𝑥ₛ τₛ τ)

record Unifier (τ₁ τ₂ : Term) : Set
 where
  field
    u₁ u₂ : AListOfSubstitutions
    unifier-law : substituteA u₁ τ₁ ≡ substituteA u₂ τ₂

unify? : (τ₁ τ₂ : Term) → Dec $ Unifier τ₁ τ₂
unify? (variable x) (variable x₁) = {!!}
unify? (variable x) (function x₁ x₂) = {!!}
unify? (function x x₁) (variable x₂) = {!!}
unify? (function 𝑓₁ x₁) (function 𝑓₂ x₃) with 𝑓₁ ≟ 𝑓₂
unify? (function 𝑓₁ x₁) (function 𝑓₂ x₃) | yes refl = {!!}
unify? (function 𝑓₁ x₁) (function 𝑓₂ x₃) | no 𝑓₁≢𝑓₂ = no (λ { record { u₁ = u₁ ; u₂ = u₂ ; unifier-law = unifier-law } → {!!}})
