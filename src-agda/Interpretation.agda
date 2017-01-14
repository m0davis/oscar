
module Interpretation where

open import VariableName
open import FunctionName
open import PredicateName
open import Element
open import Elements
open import TruthValue

record Interpretation : Set
 where
  field
    μ⟦_⟧ : VariableName → Element
    𝑓⟦_⟧ : FunctionName → Elements → Element
    𝑃⟦_⟧ : PredicateName → Elements → TruthValue

open Interpretation public

open import OscarPrelude
open import Term
open import Delay
open import Vector

mutual

  τ⇑⟦_⟧ : Interpretation → {i : Size} → Term → Delay i Element
  τ⇑⟦ I ⟧ (variable 𝑥) = now $ μ⟦ I ⟧ 𝑥
  τ⇑⟦ I ⟧ (function 𝑓 τs) = 𝑓⟦ I ⟧ 𝑓 ∘ ⟨_⟩ <$> τs⇑⟦ I ⟧ τs

  τs⇑⟦_⟧ : Interpretation → {i : Size} → (τs : Terms) → Delay i (Vector Element (arity τs))
  τs⇑⟦ I ⟧ ⟨ ⟨ [] ⟩ ⟩ = now ⟨ [] ⟩
  τs⇑⟦ I ⟧ ⟨ ⟨ τ ∷ τs ⟩ ⟩ = τ⇑⟦ I ⟧ τ >>= (λ t → τs⇑⟦ I ⟧ ⟨ ⟨ τs ⟩ ⟩ >>= λ ts → now ⟨ t ∷ vector ts ⟩)

τs⇓⟦_⟧ : (I : Interpretation) → (τs : Terms) → τs⇑⟦ I ⟧ τs ⇓
τs⇓⟦ I ⟧ ⟨ ⟨ [] ⟩ ⟩ = _ , now⇓
τs⇓⟦ I ⟧ ⟨ ⟨ variable 𝑥 ∷ τs ⟩ ⟩ = _ , τs⇓⟦ I ⟧ ⟨ ⟨ τs ⟩ ⟩ ⇓>>=⇓ now⇓
τs⇓⟦ I ⟧ ⟨ ⟨ function 𝑓₁ τs₁ ∷ τs₂ ⟩ ⟩ =
  _ , τs⇓⟦ I ⟧ τs₁ ⇓>>=⇓ now⇓ >>=⇓ (τs⇓⟦ I ⟧ ⟨ ⟨ τs₂ ⟩ ⟩ ⇓>>=⇓ now⇓)

τ⇓⟦_⟧ : (I : Interpretation) → (τ : Term) → τ⇑⟦ I ⟧ τ ⇓
τ⇓⟦ I ⟧ (variable 𝑥) = _ , now⇓
τ⇓⟦ I ⟧ (function 𝑓 τs) = _ , τs⇓⟦ I ⟧ τs ⇓>>=⇓ now⇓

τ⟦_⟧ : (I : Interpretation) → {i : Size} → (τ : Term) → Element
τ⟦ I ⟧ τ = fst (τ⇓⟦ I ⟧ τ)
