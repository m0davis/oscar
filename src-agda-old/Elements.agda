
module Elements where

open import OscarPrelude
open import Arity
open import Vector
open import Element

record Elements : Set
 where
  constructor ⟨_⟩
  field
    {arity} : Arity
    elements : Vector Element arity

open Elements public

instance EqElements : Eq Elements
Eq._==_ EqElements (⟨_⟩ {𝑎₁} εs₁) (⟨_⟩ {𝑎₂} εs₂)
 with 𝑎₁ ≟ 𝑎₂
… | no 𝑎₁≢𝑎₂ = no λ {refl → 𝑎₁≢𝑎₂ refl}
… | yes refl
 with εs₁ ≟ εs₂
… | yes refl = yes refl
… | no εs₁≢εs₂ = no λ {refl → εs₁≢εs₂ refl}
