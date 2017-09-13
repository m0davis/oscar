
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.Symmetry
open import Oscar.Class.Hmap
open import Oscar.Class.Leftunit

module Oscar.Class.Hmap.Transleftidentity where

instance
  Relprop'idFromTransleftidentity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    {transitivity : Transitivity.type _∼_}
    {reflexivity : Reflexivity.type _∼_}
    {ℓ}
    ⦃ _ : Transleftidentity.class _∼_ _∼̇_ reflexivity transitivity ⦄
    ⦃ _ : ∀ {x y} → Sym.⟦ (_∼̇_ {x} {y}) ⟧ ⦄
    → ∀ {m n}
    → Hmap.class (λ (f : m ∼ n) → transitivity f reflexivity)
                 (λ (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m) → P)
                 (λ f P → π₀ (π₀ P) f)
                 (λ f P → π₀ (π₀ P) f)
  Relprop'idFromTransleftidentity .⋆ _ (_ , P₁) = P₁ $ Sym.[] transleftidentity
