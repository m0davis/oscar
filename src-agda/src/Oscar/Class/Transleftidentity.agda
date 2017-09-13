
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Leftunit
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity

module Oscar.Class.Transleftidentity where

module Transleftidentity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  (ε : Reflexivity.type _∼_)
  (transitivity : Transitivity.type _∼_)
  = ℭLASS (_∼_ ,, (λ {x y} → _∼̇_ {x} {y}) ,, (λ {x} → ε {x}) ,, (λ {x y z} → transitivity {x} {y} {z}))
          (∀ {x y} {f : x ∼ y} → Leftunit.type _∼̇_ ε (flip transitivity) f)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  {ε : Reflexivity.type _∼_}
  {transitivity : Transitivity.type _∼_}
  where
  transleftidentity = Transleftidentity.method _∼_ _∼̇_ ε transitivity

module Transleftidentity!
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : Reflexivity.class _∼_ ⦄
  ⦃ _ : Transitivity.class _∼_ ⦄
  = Transleftidentity (_∼_) (_∼̇_) reflexivity transitivity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  ⦃ _ : Reflexivity.class _∼_ ⦄
  ⦃ _ : Transitivity.class _∼_ ⦄
  where
  transleftidentity! = Transleftidentity!.method _∼_ _∼̇_

module _ where

  transleftidentity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
    ⦃ _ : Reflexivity.class _∼_ ⦄
    ⦃ _ : Transitivity.class _∼_ ⦄
    ⦃ _ : Transleftidentity!.class _∼_ _∼̇_ ⦄
    → Transleftidentity!.type _∼_ _∼̇_
  transleftidentity[ _ ] = transleftidentity

module _ where

  open import Oscar.Data.Proposequality

  module ≡̇-Transleftidentity!
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔣} (F : 𝔒 → Ø 𝔣)
    {𝔱} (T : {x : 𝔒} → F x → 𝔒 → Ø 𝔱)
    (let _∼_ : ∀ x y → Ø 𝔣 ∙̂ 𝔱
         _∼_ = λ x y → (f : F x) → T f y)
    ⦃ _ : Reflexivity.class _∼_ ⦄
    ⦃ _ : Transitivity.class _∼_ ⦄
    = Transleftidentity (_∼_) _≡̇_
