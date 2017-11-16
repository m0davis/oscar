
module TermIsomorphism where

open import OscarPrelude

open import Term
open import VariableName
open import FunctionName
open import Arity
open import Vector

open import Data.Fin using (fromℕ ; toℕ ) renaming (raise to raiseFin)
open import Unify using (i ; leaf ; _fork_) renaming (Term to STerm ; AList to SAList)
open import UnifyProof2 using (mgu-c)

raiseSTerm : ∀ {m} n {o} → o ≡ n + m → STerm m → STerm o
raiseSTerm n refl (i x) = i (raiseFin n x)
raiseSTerm n o≡n+m leaf = leaf
raiseSTerm n refl (τ₁ fork τ₂) = raiseSTerm n refl τ₁ fork raiseSTerm n refl τ₂

max' : Nat → Nat → Nat
max' x y = if x >? y then x else y

aux-lemma-m<n : ∀ {m n : Nat} → IsTrue (lessNat m n) → n ≡ n - m + m
aux-lemma-m<n {zero} {zero} _ = refl
aux-lemma-m<n {zero} {suc _} _ = auto
aux-lemma-m<n {suc _} {zero} ()
aux-lemma-m<n {suc m} {suc n} m<n = by (aux-lemma-m<n {m} {n} m<n)

aux-lemma-m≮n,n≮m : ∀ {m n : Nat} → ¬ IsTrue (lessNat m n) → ¬ IsTrue (lessNat n m) → m ≡ n
aux-lemma-m≮n,n≮m {zero} {zero} m≮n n≮m = refl
aux-lemma-m≮n,n≮m {zero} {suc n} m≮n n≮m = ⊥-elim (m≮n true)
aux-lemma-m≮n,n≮m {suc m} {zero} m≮n n≮m = ⊥-elim (n≮m true)
aux-lemma-m≮n,n≮m {suc m} {suc n} m≮n n≮m = by (aux-lemma-m≮n,n≮m {m} {n} m≮n n≮m)

max-lemma-left : ∀ {m n : Nat} → max m n ≡ max m n - m + m
max-lemma-left {m} {n} with decBool (lessNat n m)
max-lemma-left {m} {n} | yes n<m = auto
max-lemma-left {m} {n} | no n≮m with decBool (lessNat m n)
max-lemma-left {m} {n} | no n≮m | (yes m<n) = aux-lemma-m<n m<n
max-lemma-left {m} {n} | no n≮m | (no m≮n)rewrite aux-lemma-m≮n,n≮m {m} {n} m≮n n≮m = auto

max-lemma-right : ∀ {m n : Nat} → max m n ≡ max m n - n + n
max-lemma-right {m} {n} with decBool (lessNat n m)
max-lemma-right {m} {n} | yes n<m = aux-lemma-m<n n<m
max-lemma-right {m} {n} | no n≮m with decBool (lessNat m n)
max-lemma-right {m} {n} | no n≮m | (yes m<n) = auto
max-lemma-right {m} {n} | no n≮m | (no m≮n)rewrite aux-lemma-m≮n,n≮m {m} {n} m≮n n≮m = auto

_⊕_ : ∃ STerm → ∃ STerm → ∃ STerm
_⊕_ (n₁ , τ₁) (n₂ , τ₂) = max n₁ n₂ , raiseSTerm (max n₁ n₂ - n₁) (max-lemma-left {n₁}) τ₁ fork raiseSTerm (max n₁ n₂ - n₂) (max-lemma-right {n₁}) τ₂

functionNameToSTerm : FunctionName → STerm 0
functionNameToSTerm ⟨ zero ⟩ = leaf
functionNameToSTerm ⟨ suc 𝑓 ⟩ = leaf fork functionNameToSTerm ⟨ 𝑓 ⟩

mutual

  termToSTerm : Term → ∃ STerm
  termToSTerm (variable x) = _ , i (fromℕ $ name x)
  termToSTerm (function 𝑓 τs) = (_ , functionNameToSTerm 𝑓) ⊕ termsToSTerm τs

  termsToSTerm : Terms → ∃ STerm
  termsToSTerm ⟨ ⟨ [] ⟩ ⟩ = 0 , leaf
  termsToSTerm ⟨ ⟨ τ ∷ τs ⟩ ⟩ = termToSTerm τ ⊕ termsToSTerm ⟨ ⟨ τs ⟩ ⟩

sTermToFunctionName : ∀ {n} → STerm n → Maybe FunctionName
sTermToFunctionName (i x) = nothing
sTermToFunctionName leaf = just ⟨ 0 ⟩
sTermToFunctionName (i x fork t₁) = nothing
sTermToFunctionName (leaf fork t₁) = sTermToFunctionName t₁ >>= (λ { ⟨ n ⟩ → just ⟨ suc n ⟩})
sTermToFunctionName ((t fork t₁) fork t₂) = nothing

mutual

  sTermToTerm : ∀ {n} → STerm n → Maybe Term
  sTermToTerm {n} (i x) = just $ variable ⟨ toℕ x ⟩
  sTermToTerm {n} leaf = just $ function ⟨ 0 ⟩ ⟨ ⟨ [] ⟩ ⟩
  sTermToTerm {n} (t₁ fork t₂) = sTermToFunctionName t₁ >>= λ 𝑓 → sTermToTerms t₂ >>= λ τs → just $ function 𝑓 τs

  sTermToTerms : ∀ {n} → STerm n → Maybe Terms
  sTermToTerms (i x) = nothing
  sTermToTerms leaf = just ⟨ ⟨ [] ⟩ ⟩
  sTermToTerms (x fork x₁) = sTermToTerm x >>= λ τ → sTermToTerms x₁ >>= λ τs → just ⟨ ⟨ τ ∷ vector (terms τs) ⟩ ⟩

term-round-trip : ∀ τ → sTermToTerm (snd $ termToSTerm τ) ≡ just τ
term-round-trip (variable ⟨ name₁ ⟩) = {!!}
term-round-trip (function x x₁) = {!!}

open import Relation.Binary.HeterogeneousEquality.Core as H
open import Data.Product
open import Data.Fin
open import Data.Sum
open import Data.Maybe.Base
open import Data.Empty

sTerm-round-trip : ∀ {n} → (t : STerm n) → (τ : Term) → just τ ≡ sTermToTerm t → snd (termToSTerm τ) H.≅ t
sTerm-round-trip (i x) (variable .(⟨ toℕ x ⟩)) refl = {!!}
sTerm-round-trip leaf (variable x) ()
sTerm-round-trip (i x fork t₁) (variable x₁) ()
sTerm-round-trip (t₁ fork t₂) (variable x) x₁ with sTermToFunctionName t₁ | sTermToTerms t₂
sTerm-round-trip (t₁ fork t₂) (variable x) () | nothing | ttt
sTerm-round-trip (t₁ fork t₂) (variable x₁) () | just x | nothing
sTerm-round-trip (t₁ fork t₂) (variable x₂) () | just x | (just x₁)
sTerm-round-trip t (function x x₁) x₂ = {!mgu-c!}


module Parameterized (Source : Nat → Set)
                     (Target : Nat → Set)
                     (let Sub : ∀ m n → Set
                          Sub m n = Source m → Target n)
 where

  _≐'_ : {m n : Nat} -> Sub m n → Sub m n -> Set
  f ≐' g = ∀ x -> f x ≡ g x

  Property' : (m : Nat) → Set₁
  Property' m = OscarPrelude.Σ (∀ {n} → (Sub m n) → Set) λ P → ∀ {m f g} -> f ≐' g -> P {m} f -> P g

{-
data AList : Set where
  anil : AList
  _asnoc_/_ : (σ : AList) (t' : Term) (x : VariableName) → AList

aListToSAList : AList → ∃
-}
