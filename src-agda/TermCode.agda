{-# OPTIONS --allow-unsolved-metas #-}
module TermCode where

open import OscarPrelude
open import VariableName
open import FunctionName
open import Arity
open import Term
open import Vector

data TermCode : Set
 where
  variable : VariableName → TermCode
  function : FunctionName → Arity → TermCode

termCode-function-inj₁ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → 𝑓₁ ≡ 𝑓₂
termCode-function-inj₁ refl = refl

termCode-function-inj₂ : ∀ {𝑓₁ 𝑓₂ arity₁ arity₂} → TermCode.function 𝑓₁ arity₁ ≡ function 𝑓₂ arity₂ → arity₁ ≡ arity₂
termCode-function-inj₂ refl = refl

instance
  EqTermCode : Eq TermCode
  Eq._==_ EqTermCode (variable 𝑥₁) (variable 𝑥₂) with 𝑥₁ ≟ 𝑥₂
  … | yes 𝑥₁≡𝑥₂ rewrite 𝑥₁≡𝑥₂ = yes refl
  … | no 𝑥₁≢𝑥₂ = no (λ { refl → 𝑥₁≢𝑥₂ refl})
  Eq._==_ EqTermCode (variable x) (function x₁ x₂) = no (λ ())
  Eq._==_ EqTermCode (function x x₁) (variable x₂) = no (λ ())
  Eq._==_ EqTermCode (function 𝑓₁ 𝑎₁) (function 𝑓₂ 𝑎₂) = decEq₂ termCode-function-inj₁ termCode-function-inj₂ (𝑓₁ ≟ 𝑓₂) (𝑎₁ ≟ 𝑎₂)

mutual
  encodeTerm : Term → List TermCode
  encodeTerm (variable 𝑥) = variable 𝑥 ∷ []
  encodeTerm (function 𝑓 (⟨_⟩ {arity} τs)) = function 𝑓 arity ∷ encodeTerms τs

  encodeTerms : {arity : Arity} → Vector Term arity → List TermCode
  encodeTerms ⟨ [] ⟩ = []
  encodeTerms ⟨ τ ∷ τs ⟩ = encodeTerm τ ++ encodeTerms ⟨ τs ⟩

mutual

  decodeTerm : Nat → StateT (List TermCode) Maybe Term
  decodeTerm zero = lift nothing
  decodeTerm (suc n) = do
    caseM get of λ
    { [] → lift nothing
    ; (variable 𝑥 ∷ _) →
      modify (drop 1) ~|
      return (variable 𝑥)
    ; (function 𝑓 arity ∷ _) →
      modify (drop 1) ~|
      decodeFunction n 𝑓 arity }

  decodeFunction : Nat → FunctionName → Arity → StateT (List TermCode) Maybe Term
  decodeFunction n 𝑓 arity = do
    τs ← decodeTerms n arity -|
    return (function 𝑓 ⟨ τs ⟩)

  decodeTerms : Nat → (arity : Arity) → StateT (List TermCode) Maybe (Vector Term arity)
  decodeTerms n ⟨ zero ⟩ = return ⟨ [] ⟩
  decodeTerms n ⟨ suc arity ⟩ = do
    τ ← decodeTerm n -|
    τs ← decodeTerms n ⟨ arity ⟩ -|
    return ⟨ τ ∷ vector τs ⟩

.decode-is-inverse-of-encode : ∀ τ → runStateT (decodeTerm ∘ length $ encodeTerm τ) (encodeTerm τ) ≡ (just $ τ , [])
decode-is-inverse-of-encode (variable 𝑥) = refl
decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ [] ⟩ ⟩) = {!!}
decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ variable 𝑥 ∷ τs ⟩ ⟩) = {!!}
decode-is-inverse-of-encode (function 𝑓 ⟨ ⟨ function 𝑓' τs' ∷ τs ⟩ ⟩) = {!!}

module ExampleEncodeDecode where
  example-Term : Term
  example-Term =
    (function ⟨ 2 ⟩
              ⟨ ⟨ ( variable ⟨ 0 ⟩ ∷
                  function ⟨ 3 ⟩ ⟨ ⟨ variable ⟨ 2 ⟩ ∷ [] ⟩ ⟩ ∷
                  variable ⟨ 5 ⟩ ∷ [] )
                ⟩ ⟩
    )

  -- function ⟨ 2 ⟩ ⟨ 3 ⟩ ∷ variable ⟨ 0 ⟩ ∷ function ⟨ 3 ⟩ ⟨ 1 ⟩ ∷ variable ⟨ 2 ⟩ ∷ variable ⟨ 5 ⟩ ∷ []
  example-TermCodes : List TermCode
  example-TermCodes = encodeTerm example-Term

  example-TermDecode : Maybe (Term × List TermCode)
  example-TermDecode = runStateT (decodeTerm (length example-TermCodes)) example-TermCodes

  example-verified : example-TermDecode ≡ (just $ example-Term , [])
  example-verified = refl

  example-bad : runStateT (decodeTerm 2) (function ⟨ 2 ⟩ ⟨ 2 ⟩ ∷ variable ⟨ 0 ⟩ ∷ []) ≡ nothing
  example-bad = refl
