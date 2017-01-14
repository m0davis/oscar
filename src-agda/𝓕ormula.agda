
module 𝓕ormula where

open import Formula

record 𝓕ormula (Is𝓕ormula : Formula → Set) : Set
 where
  constructor ⟨_⟩
  field
    {formula} : Formula
    is𝓕ormula : Is𝓕ormula formula

pattern ⟪_,_⟫ h s = ⟨_⟩ {h} s
pattern ⟪_⟫ h = (⟨_⟩ {h} _)

open 𝓕ormula public

open import 𝓐ssertion

instance 𝓐ssertion𝓕ormula : {Is𝓕ormula : Formula → Set} → 𝓐ssertion (𝓕ormula Is𝓕ormula)
𝓐ssertion𝓕ormula = record {}

open import HasSatisfaction

instance HasSatisfaction𝓕ormula : {Is𝓕ormula : Formula → Set} → HasSatisfaction (𝓕ormula Is𝓕ormula)
HasSatisfaction._⊨_ HasSatisfaction𝓕ormula I ⟪ φ ⟫ = I ⊨ φ
