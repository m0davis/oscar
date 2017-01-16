
module TermNode where

open import OscarPrelude
open import TermCode

record TermNode : Set
 where
  inductive
  field
    children : List (TermCode × TermNode)
    number : Nat

open TermNode public

open import Membership

_child∈_ : TermCode → TermNode → Set
_child∈_ 𝔠 𝔫 = 𝔠 ∈ (fst <$> children 𝔫)

_child∉_ : TermCode → TermNode → Set
𝔠 child∉ 𝔫 = ¬ (𝔠 child∈ 𝔫)

open import DecidableMembership

_child∈?_ : (𝔠 : TermCode) → (𝔫 : TermNode) → Dec $ 𝔠 child∈ 𝔫
c child∈? record { children = cs } = c ∈? (fst <$> cs)

getChild : {𝔠 : TermCode} → (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode
getChild {𝔠} (record { children = [] ; number = number₁ }) ()
getChild {._} (record { children = (fst₁ , snd₁) ∷ children₁ ; number = number₁ }) zero = snd₁
getChild {𝔠} (𝔫@record { children = x ∷ children₁ ; number = number₁ }) (suc x₁) = getChild record 𝔫 { children = children₁ } x₁

addChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∉ 𝔫 → TermNode → TermNode
addChild {𝔠} 𝔫 𝔠∉𝔫 𝔫' =
  record 𝔫 { children = (𝔠 , 𝔫') ∷ children 𝔫 }

setChild : {𝔠 : TermCode} (𝔫 : TermNode) → 𝔠 child∈ 𝔫 → TermNode → TermNode
setChild {𝔠} record { children = [] ; number = number₁ } () 𝔫'
setChild 𝔫@record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (zero) 𝔫' =
  record 𝔫 { children = ((fst₁ , 𝔫') ∷ children₁) }
setChild {𝔠} 𝔫@record { children = (x ∷ children₁) ; number = number₁ } (suc 𝔠∈𝔫) 𝔫' =
  record 𝔫 { children = (x ∷ children (setChild (record 𝔫 { children = children₁ }) 𝔠∈𝔫 𝔫')) }

setGet-ok : ∀ {𝔠} 𝔫 → (𝔠∈𝔫 : 𝔠 child∈ 𝔫) → setChild 𝔫 𝔠∈𝔫 (getChild 𝔫 𝔠∈𝔫) ≡ 𝔫
setGet-ok record { children = [] ; number = number₁ } ()
setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (zero) = refl
setGet-ok record { children = ((fst₁ , snd₁) ∷ children₁) ; number = number₁ } (suc 𝔠∈𝔫) rewrite setGet-ok (record { children = children₁ ; number = number₁ }) 𝔠∈𝔫 = refl

storeTermCodes : List TermCode → Nat → StateT TermNode Identity Nat
storeTermCodes [] 𝔑 = return 𝔑
storeTermCodes (𝔠 ∷ 𝔠s) 𝔑 =
  𝔫 ← get -|
  case 𝔠 child∈? 𝔫 of λ
  { (no 𝔠∉tests) →
    let 𝔑' , 𝔫' = runIdentity $
                  runStateT
                    (storeTermCodes 𝔠s $ suc 𝔑)
                    (record
                      { children = []
                      ; number = suc 𝔑 }) in
    put ((addChild 𝔫 𝔠∉tests 𝔫')) ~|
    return 𝔑'
  ; (yes 𝔠∈tests) →
    let 𝔑' , 𝔫' = runIdentity $
                  runStateT
                    (storeTermCodes 𝔠s $ suc 𝔑)
                    ((getChild 𝔫 𝔠∈tests)) in
    put ((setChild 𝔫 𝔠∈tests 𝔫')) ~|
    return 𝔑' }

storeTermCodes[] : (𝔫 : TermNode) (𝔑 : Nat) → (runIdentity $ runStateT (storeTermCodes [] 𝔑) 𝔫) ≡ (𝔑 , 𝔫)
storeTermCodes[] 𝔫 𝔑 = refl

--{-# REWRITE storeTermCodes[] #-}

storeTermCodes' : List TermCode → StateT Nat (StateT TermNode Identity) ⊤
storeTermCodes' 𝔠s =
  𝔑 ← get -|
  tn ← lift get -|
  (let 𝔑' , tn' = runIdentity $ runStateT (storeTermCodes 𝔠s 𝔑) tn in
   put 𝔑' ~| lift (put tn') ~| return tt)

open import Term
open import Vector

mutual

  storeTerm : Term → StateT Nat (StateT TermNode Identity) ⊤
  storeTerm τ@(variable _) = storeTermCodes' (encodeTerm τ)
  storeTerm τ@(function _ τs) = storeTermCodes' (encodeTerm τ) ~| storeTerms τs

  storeTerms : Terms → StateT Nat (StateT TermNode Identity) ⊤
  storeTerms ⟨ ⟨ [] ⟩ ⟩ = return tt
  storeTerms ⟨ ⟨ τ ∷ τs ⟩ ⟩ = storeTerm τ ~| storeTerms ⟨ ⟨ τs ⟩ ⟩ ~| return tt

module ExampleStoreTerm where

  open import FunctionName
  open import VariableName

  example-Term₁ : Term
  example-Term₁ =
    (function ⟨ 2 ⟩
              ⟨ ⟨ variable ⟨ 0 ⟩
              ∷ function ⟨ 3 ⟩
                         ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩
              ∷ variable ⟨ 5 ⟩
              ∷ []
              ⟩ ⟩
    )

  example-Term₂ : Term
  example-Term₂ =
    (function ⟨ 2 ⟩
              ⟨ ⟨ variable ⟨ 0 ⟩
              ∷ variable ⟨ 2 ⟩
              ∷ function ⟨ 3 ⟩
                         ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩
              ∷ variable ⟨ 5 ⟩
              ∷ []
              ⟩ ⟩
    )

  topNode : TermNode
  topNode = record { children = [] ; number = 0 }

  example-storeTerm : (⊤ × Nat) × TermNode
  example-storeTerm = runIdentity $ runStateT (runStateT (storeTerm example-Term₁ >> storeTerm example-Term₂) 0) topNode

NodeStateT = StateT TermNode
TopNodeState = StateT Nat (NodeStateT Identity)

open import LiteralFormula
open import IsLiteralFormula

storeLiteralFormulaTerms : LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤
storeLiteralFormulaTerms ⟨ atomic 𝑃 τs ⟩ = storeTerms τs
storeLiteralFormulaTerms ⟨ logical 𝑃 τs ⟩ = storeTerms τs

open import 𝓢equent

storeSequentLiteralFormulaTerms : 𝓢equent LiteralFormula → StateT Nat (StateT TermNode Identity) ⊤′
storeSequentLiteralFormulaTerms (φˢs ⊢ φᵗ) = sequence $ storeLiteralFormulaTerms <$> ({!φᵗ!} ∷ φˢs)
