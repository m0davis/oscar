
module TermByFunctionNames where

open import OscarPrelude
open import VariableName
open import FunctionName

data TermByFunctionNames : Nat → Set
 where
  variable : VariableName → TermByFunctionNames zero
  function : FunctionName → {arity : Nat} → (τs : Vec (Σ Nat TermByFunctionNames) arity) → {n : Nat} → n ≡ sum (vecToList $ (fst <$> τs)) → TermByFunctionNames (suc n)

mutual
  eqTermByFunctionNames : ∀ {n} → (x y : TermByFunctionNames n) → Dec (x ≡ y)
  eqTermByFunctionNames = {!!}
{-
  eqTermByFunctionNames : ∀ {n} → (x y : TermByFunctionNames n) → Dec (x ≡ y)
  eqTermByFunctionNames {.0} (variable x) (variable x₁) = {!!}
  eqTermByFunctionNames {.(suc n)} (function x {arity = arity₁} τs {n = n} x₁) (function x₂ {arity = arity₂} τs₁ {n = .n} x₃) with x ≟ x₂ | arity₁ ≟ arity₂
  eqTermByFunctionNames {.(suc n)} (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) with eqTermByFunctionNamess τs τs₁
  eqTermByFunctionNames {.(suc n)} (function x₁ {arity₁} τs {n} x₄) (function .x₁ {.arity₁} .τs {.n} x₅) | yes refl | (yes refl) | (yes refl) rewrite x₄ | x₅ = yes refl
  eqTermByFunctionNames {.(suc n)} (function x₁ {arity₁} τs {n} x₄) (function .x₁ {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) | (no x) = {!!}
  eqTermByFunctionNames {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | yes x₁ | (no x₃) = {!!}
  eqTermByFunctionNames {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (yes x₃) = {!!}
  eqTermByFunctionNames {.(suc n)} (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (no x₃) = {!!}
-}
  eqTermByFunctionNamess : ∀ {n} → (x y : Vec (Σ Nat TermByFunctionNames) n) → Dec (x ≡ y)
  eqTermByFunctionNamess {.0} [] [] = {!!}
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) with fst₁ ≟ fst₂
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl with eqTermByFunctionNames snd₁ snd₂
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl with eqTermByFunctionNamess x₁ y
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl | yes refl = yes refl
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | yes refl | no ref = {!!}
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | yes refl | no ref = {!!}
  eqTermByFunctionNamess (_∷_ {n = n} (fst₁ , snd₁) x₁) (_∷_ {n = .n} (fst₂ , snd₂) y) | no ref = {!!}

instance EqTermByFunctionNames : ∀ {n} → Eq (TermByFunctionNames n)
Eq._==_ EqTermByFunctionNames = eqTermByFunctionNames

{-
instance EqTermByFunctionNames : ∀ {n} → Eq (TermByFunctionNames n)
Eq._==_ EqTermByFunctionNames (variable x) (variable x₁) = {!!}
Eq._==_ EqTermByFunctionNames (function x {arity = arity₁} τs {n = n} x₁) (function x₂ {arity = arity₂} τs₁ {n = .n} x₃) with x ≟ x₂ | arity₁ ≟ arity₂
Eq._==_ EqTermByFunctionNames (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) with τs ≟ τs₁
Eq._==_ EqTermByFunctionNames (function x {arity₁} τs {n} x₄) (function .x {.arity₁} τs₁ {.n} x₅) | yes refl | (yes refl) | τs≡τs₁ = {!!}
Eq._==_ EqTermByFunctionNames (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | yes x₁ | (no x₃) = {!!}
Eq._==_ EqTermByFunctionNames (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (yes x₃) = {!!}
Eq._==_ EqTermByFunctionNames (function x {arity₁} τs {n} x₄) (function x₂ {arity₂} τs₁ {.n} x₅) | no x₁ | (no x₃) = {!!}
-}
