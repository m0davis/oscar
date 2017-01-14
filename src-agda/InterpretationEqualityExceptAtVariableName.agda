
module InterpretationEqualityExceptAtVariableName where

open import OscarPrelude
open import VariableName
open import FunctionName
open import PredicateName
open import Elements
open import Interpretation

record _≞_/_ (𝓘 : Interpretation) (I : Interpretation) (𝑥 : VariableName) : Set
 where
  field
    μEquality : {𝑥′ : VariableName} → 𝑥′ ≢ 𝑥 → μ⟦ 𝓘 ⟧ 𝑥 ≡ μ⟦ I ⟧ 𝑥′
    𝑓Equality : (𝑓 : FunctionName) (μs : Elements) → 𝑓⟦ 𝓘 ⟧ 𝑓 μs ≡ 𝑓⟦ I ⟧ 𝑓 μs
    𝑃Equality : (𝑃 : PredicateName) → (μs : Elements) → 𝑃⟦ 𝓘 ⟧ 𝑃 μs ≡ 𝑃⟦ I ⟧ 𝑃 μs
