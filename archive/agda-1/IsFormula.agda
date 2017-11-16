
module IsFormula where

open import Formula

data IsFormula : Formula → Set
 where
  ⟨_⟩ : (φ : Formula) → IsFormula φ
