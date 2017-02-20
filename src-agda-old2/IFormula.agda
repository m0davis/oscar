
module IFormula where

open import Agda.Primitive

record IFormula {a} (A : Set a) : Set (lsuc a) where
  field
    carrier : Set a
