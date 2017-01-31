{-# OPTIONS --allow-unsolved-metas #-}
module FindTermNode where

open import TermNode
open import OscarPrelude

record FindTermNode (A : Set) : Set
 where
  field
    findTermNode : A → TermNode → Maybe TermNode

open FindTermNode ⦃ … ⦄ public

open import TermCode
open import Term
open import Element

instance
  FindTermNodeTermCode : FindTermNode TermCode
  FindTermNode.findTermNode FindTermNodeTermCode termCode record { children = [] ; number = number₁ } = nothing
  FindTermNode.findTermNode FindTermNodeTermCode termCode 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } = ifYes fst₁ ≟ termCode then just snd₁ else findTermNode termCode record 𝔫 { children = children₁ }

  FindTermNodeTermCodes : FindTermNode (List TermCode)
  FindTermNode.findTermNode FindTermNodeTermCodes [] node = just node
  FindTermNode.findTermNode FindTermNodeTermCodes (x ∷ termCodes) node = join $ findTermNode termCodes <$> findTermNode x node

  FindTermNodeTerm : FindTermNode Term
  FindTermNode.findTermNode FindTermNodeTerm term node = findTermNode (encodeTerm term) node

-- This is starting to get difficult. We need Agda to know that the Term is encoded in the TermNode. Then we can drop the Maybe
getInterpretationOfTerm : Term → TermNode → Maybe Element
getInterpretationOfTerm τ node = ⟨_⟩ ∘ number <$> findTermNode (encodeTerm τ) node

open import Membership

FindTermNodeTermCode-ok : ∀ {𝔠 𝔫} → 𝔠 child∈ 𝔫 → IsJust (findTermNode 𝔠 𝔫)
FindTermNodeTermCode-ok {𝔠} {record { children = [] ; number = number₁ }} ()
--FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case (fst₁ ≟_) 𝔠 , graphAt {B = λ 𝑐 → Dec (fst₁ ≡ 𝑐)} (fst₁ ≟_) 𝔠 of λ { (yes x , snd₂) → {!!} ; (no x , snd₂) → {!!}} --λ { ((yes ===) , (inspect s1)) → {!!} ; ((no =n=) , inspect s2) → {!!} }
--FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ = case fst₁ ≟ 𝔠 of λ { (yes refl) → {!!} ; (no x) → {!!}}
FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ with fst₁ ≟ 𝔠
FindTermNodeTermCode-ok {𝔠} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} x₁ | yes eq2 = tt
FindTermNodeTermCode-ok {.fst₁} {record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (zero) | no neq = ⊥-elim (neq refl)
FindTermNodeTermCode-ok {𝔠} {𝔫@record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }} (suc x₁) | no neq = FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} x₁

Justified : ∀ {a} {A : Set a} → (m : Maybe A) → IsJust m → ∃ λ x → m ≡ just x
Justified nothing ()
Justified (just x) x₁ = _ , refl

open import FunctionName
open import Vector

storeTerm-ok : ∀ τ 𝔫 𝔑 → IsJust (findTermNode τ (snd (runIdentity (runStateT (runStateT (storeTerm τ) 𝔑) 𝔫))))
storeTerm-ok (variable 𝑥) 𝔫 𝔑 with variable 𝑥 child∈? 𝔫
storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x with TermCode.variable 𝑥 ≟ variable 𝑥
storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x | yes _ = tt
storeTerm-ok (variable 𝑥) 𝔫 𝔑 | no x | no variable𝑥≢variable𝑥 = ⊥-elim (variable𝑥≢variable𝑥 refl)
--storeTerm-ok (variable 𝑥) 𝔫 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 = {!𝔫!}
storeTerm-ok (variable 𝑥) record { children = [] ; number = number₁ } 𝔑 | yes ()
--storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 = {!!}
storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 rewrite setGet-ok 𝔫 vx∈𝔫 with fst₁ ≟ variable 𝑥
storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | yes eq = tt
--… | no neq = case vx∈𝔫 of λ { (here .(map fst children₁)) → ⊥-elim (neq refl)  ; (there .fst₁ asdf) → case graphAt FindTermNodeTermCode-ok asdf of λ { (ingraph sss) → {!!} } } -- storeTerm-ok x {!record 𝔫 { children = children₁ }!} 𝔑 -- x record 𝔫 { children = children₁ } 𝔑
--… | no neq = case vx∈𝔫 of λ { (here .(map fst children₁)) → ⊥-elim (neq refl)  ; (there .fst₁ asdf) → case inspect $ FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} asdf of λ { (.(FindTermNodeTermCode-ok asdf) , ingraph refl) → {!!}} } -- storeTerm-ok x {!record 𝔫 { children = children₁ }!} 𝔑 -- x record 𝔫 { children = children₁ } 𝔑
storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq with vx∈𝔫
storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | zero = ⊥-elim (neq refl)
--storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | there dfdsf fdsdfs with FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs | graphAt (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }}) fdsdfs
--… | frfrrf | ingraph tttttt = transport _ (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) _
storeTerm-ok x@(variable 𝑥) 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } 𝔑 | yes vx∈𝔫 | no neq | suc fdsdfs rewrite (snd $ Justified (FindTermNode.findTermNode FindTermNodeTermCode (variable 𝑥) (record { children = children₁ ; number = number₁ })) (FindTermNodeTermCode-ok {𝔫 = record 𝔫 { children = children₁ }} fdsdfs)) = tt
storeTerm-ok (function 𝑥 𝑎) 𝔫 𝔑 with (function 𝑥 (arity 𝑎)) child∈? 𝔫
storeTerm-ok (function 𝑥 ⟨ ⟨ [] ⟩ ⟩) 𝔫 𝔑 | no x with Eq._==_ EqFunctionName ⟨ name 𝑥 ⟩ ⟨ name 𝑥 ⟩
storeTerm-ok (function 𝑥 ⟨ ⟨ [] ⟩ ⟩) 𝔫 𝔑 | no x | (yes refl) = tt
… | no neq = ⊥-elim (neq refl)
--storeTerm-ok τ₀@(function 𝑓 ⟨ τ₁ ∷ τ₂s ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!τ₁!}
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₁∉𝔫 with variable 𝑥 child∈? 𝔫
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) with 𝑓₀ ≟ 𝑓₀
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl with TermCode.variable 𝑥 ≟ variable 𝑥
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | yes eq = tt
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | yes refl | no neq = ⊥-elim (neq refl)
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥 ∷ []        ⟩ ⟩) 𝔫 𝔑        | no 𝔠₀∉𝔫 | (yes 𝔠₁∈𝔫) | no neq = ⊥-elim (neq refl)
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) with 𝑓₀ ≟ 𝑓₀
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl with TermCode.variable 𝑥₁ ≟ variable 𝑥₁
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | yes 𝔠₁≡𝔠₁ = tt
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | yes refl | no 𝔠₁≢𝔠₁ = ⊥-elim (𝔠₁≢𝔠₁ refl)
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ []       ⟩ ⟩) 𝔫 𝔑       | no 𝔠₀∉𝔫 | (no 𝔠₁∉𝔫) | no 𝑓₀≢𝑓₀ = ⊥-elim (𝑓₀≢𝑓₀ refl) -- rewrite setGet-ok 𝔫 𝔠₁∈𝔫
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 with variable 𝑥₁ child∈? 𝔫
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | yes 𝔠₁∈𝔫 = {!!}
storeTerm-ok (function 𝑓₀ ⟨ ⟨ variable 𝑥₁ ∷ τ₂ ∷ τ₃s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₀∉𝔫 | no 𝔠₁∉𝔫 = {!!}
storeTerm-ok τ₀@(function 𝑓₀ ⟨ ⟨ function 𝑓₁ τ₁s ∷ τ₂s ⟩ ⟩) 𝔫 𝔑 | no 𝔠₁∉𝔫 = {!!}
storeTerm-ok (function 𝑥 x₁) 𝔫 𝔑 | yes x = {!!}

mutual

  storeTermVerifiably' : (τ : Term) → StateT Nat (StateT (Σ TermNode λ n → IsJust (findTermNode τ n)) Identity) ⊤
  storeTermVerifiably' (variable x) = {!!}
  storeTermVerifiably' (function x x₁) = {!!}

  storeTermVerifiably : Term → StateT Nat (StateT TermNode Identity) ⊤
  storeTermVerifiably τ@(variable _) = storeTermCodes' (encodeTerm τ)
  storeTermVerifiably τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTermsVerifiably τs

  storeTermsVerifiably : Terms → StateT Nat (StateT TermNode Identity) ⊤
  storeTermsVerifiably ⟨ ⟨ [] ⟩ ⟩ = return tt
  storeTermsVerifiably ⟨ ⟨ τ ∷ τs ⟩ ⟩ = storeTermVerifiably τ ~| storeTermsVerifiably ⟨ ⟨ τs ⟩ ⟩ ~| return tt
